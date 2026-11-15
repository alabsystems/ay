// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a term is, by content (design H2).
//!
//! `TermData` has no op-kind enum yet (design T3), so operators are named by
//! their symbol. The registry is conservative: an application is
//! uninterpreted only when its symbol is none of the interpreted names below
//! and every sort it touches is Bool, Int, Real or an uninterpreted sort.
//! Anything else is named in a give-up before the search starts.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

use crate::plugin::GiveUp;
use crate::term_key::TermKeys;

/// Boolean connectives Tseitin encodes.
const CONNECTIVES: [&str; 4] = ["and", "or", "xor", "=>"];
/// Arithmetic comparisons.
pub(crate) const COMPARISONS: [&str; 4] = ["<=", "<", ">=", ">"];
/// Linear arithmetic operators the LRA parser interprets.
const LINEAR: [&str; 4] = ["+", "-", "*", "/"];
/// Interpreted arithmetic operators the arithmetic plug-in defines in the
/// search when their shape allows (`linear.rs` names the shapes it refuses).
const DEFINED_ARITH: [&str; 3] = ["div", "mod", "abs"];
/// Interpreted arithmetic operators no plug-in serves yet.
const OTHER_ARITH: [&str; 3] = ["to_int", "to_real", "is_int"];

/// Whether a sort is one the kernel's plug-ins cover.
pub(crate) fn covered_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::Real | Sort::Uninterpreted(_)
    )
}

/// Whether a sort is arithmetic.
pub(crate) fn arithmetic(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

/// An internal symbol namespace: never an uninterpreted function, unless
/// the declaring layer registered the name as the private identity of a user
/// declaration (a re-declaration after `pop`, or a builtin's name such as
/// `abs`, is spelled `__ay_overload_N`): user-declared symbols are
/// uninterpreted whatever their spelling.
fn internal_name(terms: &TermStore, name: &str) -> bool {
    (name.starts_with('@') || name.starts_with("__ay") || name.starts_with("!ay."))
        && !terms.is_declared_function(name)
}

/// Whether `term` is an application of an uninterpreted function symbol
/// (with at least one argument) over covered sorts.
pub(crate) fn is_uf_app(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return false;
    };
    if args.is_empty() {
        return false;
    }
    let name: &str = name;
    let interpreted = name == "="
        || name == "distinct"
        || name == "not"
        || name == "ite"
        || CONNECTIVES.contains(&name)
        || COMPARISONS.contains(&name)
        || LINEAR.contains(&name)
        || DEFINED_ARITH.contains(&name)
        || OTHER_ARITH.contains(&name)
        || internal_name(terms, name);
    !interpreted
        && covered_sort(terms.sort(term))
        && args.iter().all(|&a| covered_sort(terms.sort(a)))
}

/// What a scan of the assertions found.
#[derive(Debug, Default)]
pub(crate) struct Scan {
    /// Uninterpreted applications, arguments before parents.
    pub(crate) uf_apps: Vec<TermId>,
    /// Boolean arguments of uninterpreted applications: each needs a SAT
    /// variable so the hub can merge it with `true` or `false`.
    pub(crate) bool_args: Vec<TermId>,
    /// Arithmetic term-level ites (the arithmetic plug-in's): the search
    /// starts with their link definitions `¬c ∨ (= (ite c a b) a)` and
    /// `c ∨ (= (ite c a b) b)`, so each condition needs a SAT variable even
    /// when it occurs nowhere else (an `and` condition used to be minted as
    /// an atom no plug-in owns).
    pub(crate) arith_ites: Vec<TermId>,
    /// A term of an uninterpreted sort occurs (EUF is needed even without
    /// an application, for `(= a b)` over constants).
    pub(crate) uninterpreted_sort: bool,
}

/// Walk the assertions once: refuse, before the search, every construct no
/// plug-in serves (naming it), and collect the uninterpreted applications.
pub(crate) fn scan(terms: &TermStore, roots: &[TermId]) -> Result<Scan, GiveUp> {
    let mut out = Scan::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut bool_args: HashSet<TermId> = HashSet::default();
    // (term, children pushed): post-order so arguments precede applications.
    let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&r| (r, false)).collect();
    while let Some((term, expanded)) = stack.pop() {
        if expanded {
            if is_uf_app(terms, term) {
                out.uf_apps.push(term);
            }
            continue;
        }
        if !seen.insert(term) {
            continue;
        }
        let children = check_node(terms, term)?;
        if terms.sort(term).is_uninterpreted() {
            out.uninterpreted_sort = true;
        }
        if is_uf_app(terms, term) {
            if let TermData::App(_, args) = terms.get(term) {
                for &a in args {
                    if terms.sort(a) == &Sort::Bool && bool_args.insert(a) {
                        out.bool_args.push(a);
                    }
                }
            }
        }
        if matches!(terms.get(term), TermData::Ite(..)) && arithmetic(terms.sort(term)) {
            out.arith_ites.push(term);
        }
        stack.push((term, true));
        stack.extend(children.into_iter().map(|c| (c, false)));
    }
    Ok(out)
}

/// Validate one node and return its children.
fn check_node(terms: &TermStore, term: TermId) -> Result<Vec<TermId>, GiveUp> {
    let sort = terms.sort(term);
    if !covered_sort(sort) {
        return Err(GiveUp::new(format!("no plug-in serves sort {sort:?}")));
    }
    match terms.get(term) {
        TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => {
            Ok(Vec::new())
        }
        TermData::Const(c) => Err(GiveUp::new(format!("no plug-in serves constant {c:?}"))),
        TermData::Var(..) => Ok(Vec::new()),
        TermData::Not(inner) => Ok(vec![*inner]),
        TermData::Ite(c, t, e) => {
            // An arithmetic ite inside an arithmetic atom is the arithmetic
            // plug-in's (its link lemmas); every other term-level ite was
            // named by internalization when the hub has work.
            if sort == &Sort::Bool || arithmetic(sort) {
                Ok(vec![*c, *t, *e])
            } else {
                Err(GiveUp::new("a term-level ite survived internalization"))
            }
        }
        TermData::App(Symbol::Indexed(name, _), _) => Err(GiveUp::new(format!(
            "no plug-in owns indexed operator `{name}`"
        ))),
        TermData::App(Symbol::Named(name), args) => {
            let name: &str = name;
            if args.is_empty() {
                // A constant of a covered sort, internal (a preprocessing
                // name) or declared.
                return Ok(Vec::new());
            }
            if is_uf_app(terms, term) || CONNECTIVES.contains(&name) || name == "not" {
                return Ok(args.clone());
            }
            if name == "=" {
                return if args.len() == 2 {
                    Ok(args.clone())
                } else {
                    Err(GiveUp::new("an n-ary `=` survived internalization"))
                };
            }
            if COMPARISONS.contains(&name) {
                return Ok(args.clone());
            }
            if LINEAR.contains(&name) {
                linear(terms, name, args)?;
                return Ok(args.clone());
            }
            if DEFINED_ARITH.contains(&name) {
                // The linearizer names a shape the plug-in cannot define.
                return Ok(args.clone());
            }
            Err(GiveUp::new(format!("no plug-in owns operator `{name}`")))
        }
        TermData::Let(..) => Err(GiveUp::new("a `let` survived internalization")),
        TermData::Forall(..) | TermData::Exists(..) => {
            Err(GiveUp::new("no plug-in owns quantifiers"))
        }
        _ => Err(GiveUp::new("no plug-in owns this kind of term")),
    }
}

/// `*` with at most one non-constant factor and `/` by a non-zero constant:
/// what the LRA tableau interprets exactly.
fn linear(terms: &TermStore, op: &str, args: &[TermId]) -> Result<(), GiveUp> {
    match op {
        "*" => {
            let symbolic = args.iter().filter(|&&a| !is_constant(terms, a)).count();
            if symbolic > 1 {
                return Err(GiveUp::new(
                    "nonlinear `*`: needs the nonlinear module (roadmap AN)",
                ));
            }
        }
        "/" => {
            let divisor_ok = args.len() == 2 && is_nonzero_constant(terms, args[1]);
            if !divisor_ok {
                return Err(GiveUp::new(
                    "`/` by a non-constant: needs the nonlinear module (roadmap AN)",
                ));
            }
        }
        _ => {}
    }
    Ok(())
}

/// A numeral, or arithmetic over numerals only.
fn is_constant(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
        TermData::App(Symbol::Named(name), args) if LINEAR.contains(&name.as_ref()) => {
            args.iter().all(|&a| is_constant(terms, a))
        }
        _ => false,
    }
}

fn is_nonzero_constant(terms: &TermStore, term: TermId) -> bool {
    use num_traits::Zero;
    match terms.get(term) {
        TermData::Const(Constant::Int(i)) => !i.is_zero(),
        TermData::Const(Constant::Rational(r)) => !r.0.is_zero(),
        TermData::App(Symbol::Named(name), args) if name.as_ref() == "-" && args.len() == 1 => {
            is_nonzero_constant(terms, args[0])
        }
        _ => false,
    }
}

/// The uninterpreted applications in canonical order (KC9): by height, so
/// arguments precede their applications, then by content key, so the hub's
/// node numbering (which decides class representatives, table entries and
/// the order of its events) never follows the order terms were interned in.
pub(crate) fn canonical_apps(terms: &TermStore, apps: &[TermId]) -> Vec<TermId> {
    let mut heights: HashMap<TermId, u32> = HashMap::default();
    let mut keys = TermKeys::default();
    let mut out = apps.to_vec();
    out.sort_by_cached_key(|&app| (height(terms, app, &mut heights), keys.key(terms, app), app));
    out
}

/// The height of a term (leaves are 0), memoized.
fn height(terms: &TermStore, root: TermId, memo: &mut HashMap<TermId, u32>) -> u32 {
    let mut stack = vec![(root, false)];
    while let Some((t, expanded)) = stack.pop() {
        if memo.contains_key(&t) {
            continue;
        }
        let kids: Vec<TermId> = match terms.get(t) {
            TermData::App(_, args) => args.clone(),
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Not(inner) => vec![*inner],
            _ => Vec::new(),
        };
        if !expanded && kids.iter().any(|k| !memo.contains_key(k)) {
            stack.push((t, true));
            stack.extend(kids.into_iter().map(|k| (k, false)));
            continue;
        }
        let h = kids
            .iter()
            .filter_map(|k| memo.get(k))
            .max()
            .map_or(0, |m| m.saturating_add(1));
        memo.insert(t, h);
    }
    memo.get(&root).copied().unwrap_or(0)
}
