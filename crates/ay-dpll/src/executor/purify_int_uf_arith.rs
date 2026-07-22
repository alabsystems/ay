// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen purification of opaque Int-sorted uninterpreted-function
//! applications that appear inside arithmetic expressions.
//!
//! When an opaque (uninterpreted) Int-sorted function application such as
//! `(__euclid!div a b)` or `(__euclid!mod a b)` appears as an operand of an
//! arithmetic operator — e.g. inside `(* b (__euclid!div a b))` or
//! `(+ ... (__euclid!mod a b))` — the LRA/NIA layer can only treat it as an
//! opaque slack that it cannot relate to the surrounding arithmetic. A shared
//! (dis)equality over such a term never resolves: LRA reports the operand as an
//! "Unknown function" and requests an expression split, but the split atoms
//! still contain the same opaque operands, so the loop never converges. A
//! genuinely satisfiable formula can then stall to `unknown`.
//!
//! Concretely, the Euclidean reconstruction obligation
//! `(a / b) * b + a % b == a` with NO `b != 0` premise — where `/` and `%` are
//! encoded as the uninterpreted `__euclid!div` / `__euclid!mod` (Verus spec
//! div/mod-by-zero is unspecified, so they must stay uninterpreted) — has the
//! genuine model `b = 0` (`b * div(a,0) = 0`, `a != mod(a,0)`), but the negated
//! obligation `a != (b*div + mod)` never resolves because `div` sits inside the
//! nonlinear product `b*div` and `mod` sits bare, both opaque to LRA/NIA.
//!
//! This pass replaces each such application `u` with a fresh Int variable `v`
//! and appends the defining assertion `(= v u)`. The fresh `v` is a first-class
//! arithmetic variable that LRA/NIA registers and shares across the N-O
//! interface (so the product becomes a genuine `b*v` monomial and the bare
//! occurrence becomes a splittable variable), while the linking equality keeps
//! `v` definitionally equal to `u` in EUF. The rewrite is EQUISATISFIABLE — `v`
//! is fresh and fully defined by `v = u`, so it can neither add nor remove a
//! model, hence it can never cause a wrong-SAT or wrong-UNSAT.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

/// Arithmetic operators whose Int-sorted operands are candidates for
/// purification when they are opaque uninterpreted applications.
fn is_arith_op(name: &str) -> bool {
    matches!(name, "+" | "-" | "*" | "/" | "div" | "mod" | "abs")
}

/// Comparison / equality operators that bound an arithmetic *atom* — the scope
/// within which we look for the opaque-UF nonlinear product trigger and, if
/// found, purify.
fn is_atom_op(name: &str) -> bool {
    matches!(name, "<" | "<=" | ">" | ">=" | "=" | "distinct")
}

/// Builtin operators that are NOT opaque uninterpreted functions. An
/// Int-sorted `App(Named(n), _)` whose `n` is one of these is owned by an
/// arithmetic / array / SAT theory and must not be purified: arrays already
/// carry their own Nelson-Oppen interface, and arithmetic builtins are the
/// operators we purify *into*, not *out of*.
fn is_builtin(name: &str) -> bool {
    is_arith_op(name)
        || matches!(
            name,
            "<" | "<="
                | ">"
                | ">="
                | "="
                | "distinct"
                | "and"
                | "or"
                | "xor"
                | "=>"
                | "not"
                | "ite"
                | "select"
                | "store"
                | "to_real"
                | "to_int"
        )
}

/// A term is an opaque Int-sorted uninterpreted-function application iff it is
/// an `App` with a non-builtin named symbol and Int sort. Such a term is
/// exactly what LRA/NIA cannot see through inside an arithmetic expression.
fn is_opaque_int_uf(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term),
        TermData::App(Symbol::Named(n), _) if !is_builtin(n))
        && terms.sort(term) == &Sort::Int
}

/// Does `t`'s arithmetic contain a nonlinear product `(* f1 f2 ...)` with two
/// or more non-constant factors, at least one of which is an opaque Int-sorted
/// UF application? This is the precise trigger shape: an opaque UF sitting
/// inside a nonlinear monomial (e.g. `(* b (__euclid!div a b))`) is exactly
/// what LRA/NIA over-approximates as an unrelatable opaque slack, stalling a
/// shared (dis)equality split. Restricting purification to atoms with this
/// shape keeps LINEAR opaque-UF occurrences — array/seq bridge functions
/// (`seq_len`, `seq_index_logic`) and BV↔Int bridge reads (`bv2int`) that the
/// existing Nelson-Oppen interface bridge already handles — untouched, so their
/// working solves are not perturbed.
///
/// Does not descend into quantifier bodies (closed-term requirement).
fn has_opaque_nonlinear_product(
    terms: &TermStore,
    t: TermId,
    seen: &mut DetHashSet<TermId>,
) -> bool {
    if !seen.insert(t) {
        return false;
    }
    match terms.get(t).clone() {
        TermData::App(sym, args) => {
            if matches!(&sym, Symbol::Named(n) if n == "*") {
                let non_const: Vec<TermId> = args
                    .iter()
                    .copied()
                    .filter(|&a| terms.extract_integer_constant(a).is_none())
                    .collect();
                if non_const.len() >= 2 && non_const.iter().any(|&a| is_opaque_int_uf(terms, a)) {
                    return true;
                }
            }
            args.iter()
                .any(|&a| has_opaque_nonlinear_product(terms, a, seen))
        }
        TermData::Not(x) => has_opaque_nonlinear_product(terms, x, seen),
        TermData::Ite(c, th, e) => {
            has_opaque_nonlinear_product(terms, c, seen)
                || has_opaque_nonlinear_product(terms, th, seen)
                || has_opaque_nonlinear_product(terms, e, seen)
        }
        TermData::Let(binds, body) => {
            binds
                .iter()
                .any(|(_, v)| has_opaque_nonlinear_product(terms, *v, seen))
                || has_opaque_nonlinear_product(terms, body, seen)
        }
        _ => false,
    }
}

/// Collect every opaque Int-sorted UF application that appears as an operand of
/// an arithmetic operator within `atom`. Used only on atoms already known to
/// contain an opaque-UF nonlinear product.
fn collect_arith_operands(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    targets: &mut DetHashSet<TermId>,
) {
    if !seen.insert(root) {
        return;
    }
    match terms.get(root).clone() {
        TermData::App(sym, args) => {
            let is_arith = matches!(&sym, Symbol::Named(n) if is_arith_op(n));
            for &a in &args {
                if is_arith && is_opaque_int_uf(terms, a) {
                    targets.insert(a);
                }
                collect_arith_operands(terms, a, seen, targets);
            }
        }
        TermData::Not(x) => collect_arith_operands(terms, x, seen, targets),
        TermData::Ite(c, t, e) => {
            collect_arith_operands(terms, c, seen, targets);
            collect_arith_operands(terms, t, seen, targets);
            collect_arith_operands(terms, e, seen, targets);
        }
        TermData::Let(binds, body) => {
            for (_, v) in binds {
                collect_arith_operands(terms, v, seen, targets);
            }
            collect_arith_operands(terms, body, seen, targets);
        }
        TermData::Forall(..) | TermData::Exists(..) => {}
        _ => {}
    }
}

/// Walk the Boolean skeleton to arithmetic *atoms* (comparison / (dis)equality
/// applications). For each atom whose arithmetic contains an opaque-UF
/// nonlinear product, collect the opaque Int-UF arithmetic operands to purify.
/// Does not descend into quantifier bodies, so collected terms are closed
/// (capture-safe to hoist to a global proxy).
fn collect(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    targets: &mut DetHashSet<TermId>,
) {
    if !seen.insert(root) {
        return;
    }
    match terms.get(root).clone() {
        TermData::App(sym, args) => {
            let is_atom = matches!(&sym, Symbol::Named(n) if is_atom_op(n));
            if is_atom {
                let mut prod_seen = DetHashSet::default();
                if has_opaque_nonlinear_product(terms, root, &mut prod_seen) {
                    let mut op_seen = DetHashSet::default();
                    collect_arith_operands(terms, root, &mut op_seen, targets);
                }
                // Arithmetic below an atom does not contain further Boolean
                // atoms, so no need to recurse for atom discovery.
            } else {
                for &a in &args {
                    collect(terms, a, seen, targets);
                }
            }
        }
        TermData::Not(x) => collect(terms, x, seen, targets),
        TermData::Ite(c, t, e) => {
            collect(terms, c, seen, targets);
            collect(terms, t, seen, targets);
            collect(terms, e, seen, targets);
        }
        TermData::Let(binds, body) => {
            for (_, v) in binds {
                collect(terms, v, seen, targets);
            }
            collect(terms, body, seen, targets);
        }
        // Do not descend into quantifier bodies: an opaque UF operand there may
        // reference bound variables (not a closed term) and must not be hoisted
        // to a global proxy. The target fragment (QF_UF[N]IA) is
        // quantifier-free.
        TermData::Forall(..) | TermData::Exists(..) => {}
        TermData::Const(_) | TermData::Var(_, _) => {}
        // TermData is #[non_exhaustive]; unknown constructs are left
        // un-purified (conservative — never unsound).
        _ => {}
    }
}

/// True iff `term` is an Int-sorted `(mod a k)` / `(div a k)` application with a
/// non-symbolic INTEGER-CONSTANT divisor `k` — the shape `mod_div_elim`'s
/// constant path (`eliminate_int_mod_div_by_constant`) rewrites to a per-assertion
/// fresh remainder var. When such a term sits as an ARGUMENT to an uninterpreted
/// function it is invisible to EUF congruence: two syntactically-identical
/// `(mod x 3)` occurrences are eliminated to per-assertion-DISTINCT fresh
/// remainder vars, so a UF application over one is never congruence-linked to a
/// UF application over the same value expressed differently (e.g. the literal `1`
/// when `(= (mod x 3) 1)` is asserted). Naming the shared term with a single
/// proxy restores the link.
///
/// SYMBOLIC-divisor `(mod a b)` (non-constant `b`) is deliberately EXCLUDED: it
/// travels a different `mod_div_elim` path (`eliminate_int_mod_div` +
/// symbolic-divisor congruence) whose SAT model machinery — the seq/datatype
/// bridge reducers and the zero-divisor `introduced_unconstrained_div_mod`
/// branch — the proxy indirection defeats, degrading a genuine `sat` to
/// `unknown`. The congruence gap this pass repairs is specific to the constant
/// path.
fn is_int_mod_div(terms: &TermStore, term: TermId) -> bool {
    let divisor = match terms.get(term) {
        TermData::App(Symbol::Named(n), args)
            if args.len() == 2
                && matches!(n.as_str(), "mod" | "div")
                && terms.sort(term) == &Sort::Int =>
        {
            args[1]
        }
        _ => return false,
    };
    terms.extract_integer_constant(divisor).is_some()
}

/// Collect every Int-sorted `mod`/`div` application that appears as a direct
/// ARGUMENT of an uninterpreted-function application within `root`'s
/// quantifier-free skeleton. Does not descend into quantifier bodies, so every
/// collected term is closed and safe to name with a global proxy.
///
/// `targets.insert` runs on each UF-argument occurrence regardless of `seen`
/// (which only prunes re-walking a shared subtree), so a mod/div term reachable
/// both as a UF argument and elsewhere is still collected.
fn collect_mod_div_uf_args(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    targets: &mut DetHashSet<TermId>,
) {
    match terms.get(root).clone() {
        TermData::App(sym, args) => {
            let is_uf = matches!(&sym, Symbol::Named(n) if !is_builtin(n));
            for &a in &args {
                if is_uf && is_int_mod_div(terms, a) {
                    targets.insert(a);
                }
            }
            if !seen.insert(root) {
                return;
            }
            for &a in &args {
                collect_mod_div_uf_args(terms, a, seen, targets);
            }
        }
        TermData::Not(x) => {
            if seen.insert(root) {
                collect_mod_div_uf_args(terms, x, seen, targets);
            }
        }
        TermData::Ite(c, t, e) => {
            if seen.insert(root) {
                collect_mod_div_uf_args(terms, c, seen, targets);
                collect_mod_div_uf_args(terms, t, seen, targets);
                collect_mod_div_uf_args(terms, e, seen, targets);
            }
        }
        TermData::Let(binds, body) => {
            if seen.insert(root) {
                for (_, v) in binds {
                    collect_mod_div_uf_args(terms, v, seen, targets);
                }
                collect_mod_div_uf_args(terms, body, seen, targets);
            }
        }
        // Do not descend into quantifier bodies: a mod/div operand there may
        // reference bound variables (not a closed term) and must not be hoisted
        // to a global proxy. The target fragment (QF_UF[N]IA) is
        // quantifier-free.
        TermData::Forall(..) | TermData::Exists(..) => {}
        TermData::Const(_) | TermData::Var(_, _) => {}
        _ => {}
    }
}

/// Purify Int-sorted `mod`/`div` applications that appear as ARGUMENTS to an
/// uninterpreted function.
///
/// Replaces each such shared term `u = (mod a k)` / `(div a k)` with ONE fresh
/// Int proxy `v` — rewriting EVERY occurrence of `u` across all assertions (so
/// `(= (mod x 3) 1)` becomes `(= v 1)` and `(f (mod x 3))` becomes `(f v)`) —
/// and appends the single defining assertion `(= v u)`. This exposes the shared
/// value to EUF congruence: with `(= v 1)` and `(f v)` both present, congruence
/// derives `f(v) = f(1)`, which `mod_div_elim`'s per-assertion-distinct
/// remainder vars otherwise hide.
///
/// Returns `true` if any purification occurred; a no-op (immediate `false`) when
/// no mod/div sits under a UF. Equisatisfiable: `v` is fresh and fully defined
/// by `v = u`, so it adds no model and removes none. It NEVER equates distinct
/// mod/div terms — each distinct interned term gets its own proxy, and
/// congruence over the proxies fires only when the solver proves the proxies
/// equal (exactly the sound semantics), so it can neither wrong-SAT nor
/// wrong-UNSAT.
pub(crate) fn purify_mod_div_uf_args(terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
    let mut seen = DetHashSet::default();
    let mut targets = DetHashSet::default();
    for &root in assertions.iter() {
        collect_mod_div_uf_args(terms, root, &mut seen, &mut targets);
    }
    if targets.is_empty() {
        return false;
    }

    // Deterministic order for fresh-var allocation.
    let mut ordered: Vec<TermId> = targets.iter().copied().collect();
    ordered.sort_unstable_by_key(|t| t.0);

    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut defs: Vec<TermId> = Vec::with_capacity(ordered.len());
    for u in ordered {
        let v = terms.mk_fresh_var("uf_moddiv", Sort::Int);
        map.insert(u, v);
        // Defining constraint v = u (uses the original, un-rewritten u).
        defs.push(terms.mk_eq(v, u));
    }

    for root in assertions.iter_mut() {
        *root = terms.substitute_terms(*root, &map);
    }
    assertions.extend(defs);
    true
}

/// Purify opaque Int-sorted UF applications inside arithmetic expressions.
///
/// Returns `true` if any purification occurred. Appends `(= proxy original)`
/// definitions to `assertions` and rewrites every occurrence of each purified
/// application to its fresh proxy variable. Equisatisfiable.
pub(crate) fn purify_int_uf_arith(terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
    let mut seen = DetHashSet::default();
    let mut targets = DetHashSet::default();
    for &root in assertions.iter() {
        collect(terms, root, &mut seen, &mut targets);
    }
    if targets.is_empty() {
        return false;
    }

    // Deterministic order for fresh-var allocation.
    let mut ordered: Vec<TermId> = targets.iter().copied().collect();
    ordered.sort_unstable_by_key(|t| t.0);

    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut defs: Vec<TermId> = Vec::with_capacity(ordered.len());
    for u in ordered {
        let v = terms.mk_fresh_var("uf_arith", Sort::Int);
        map.insert(u, v);
        // Defining constraint v = u (uses the original, un-rewritten u).
        defs.push(terms.mk_eq(v, u));
    }

    for root in assertions.iter_mut() {
        *root = terms.substitute_terms(*root, &map);
    }
    assertions.extend(defs);
    true
}

#[cfg(test)]
mod tests;
