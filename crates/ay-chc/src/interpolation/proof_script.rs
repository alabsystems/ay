// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIA / QF_LRA (+Bool) group scripts for the proof substrate, and the
//! sort-preserving ay-dpll `Term` → `ChcExpr` converter.
//!
//! CHC-COMP 2026 Workstream D, Rung 1 (the development design notes
//! DESIGN_lra_interp_tpa.md` §4.1). **Owner: WP-D1-P.** Generalises
//! `proof_backed.rs`'s QF_LIA-only helpers (`collect_supported_vars`,
//! `build_qf_lia_script`, `dpll_term_to_chc_expr`, `app_to_chc_expr`,
//! `parse_const_text`) to QF_LRA; the legacy QF_LIA copies stay in
//! `proof_backed.rs` so its LIA scripts and verdicts are byte-identical.
//!
//! Everything here is DAG-aware: the fragment scan visits each distinct node
//! (pointer identity) once against a unique-node cap, the script is printed
//! DAG-linearly by `smt::dag_smtlib`, and the converter memoises on the
//! ay-dpll term handle and shares converted children by `Arc` (no structural
//! hashing of the result, which is a tree walk on a DAG).

use super::proof_groups::{ItpFail, ItpUnknown};
use crate::smt::dag_smtlib::{self, DagCaps, DagStats};
use crate::smt::executor_adapter::{quote_symbol, sort_to_smtlib};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_dpll::api::{Logic, Solver, Sort as DpllSort, Term as DpllTerm, TermKind};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};
use std::sync::Arc;

/// Logic of one group script. Bool is always allowed; an Int+Real mix is
/// `Err(ItpUnknown::Fragment)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProofLogic {
    QfLia,
    QfLra,
}

impl ProofLogic {
    /// The ay-dpll logic of the proof solver.
    pub(crate) fn dpll_logic(self) -> Logic {
        match self {
            Self::QfLia => Logic::QfLia,
            Self::QfLra => Logic::QfLra,
        }
    }

    /// SMT-LIB logic name.
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::QfLia => "QF_LIA",
            Self::QfLra => "QF_LRA",
        }
    }
}

/// One proof-solve script: declarations, then the asserts group by group.
pub(crate) struct GroupScript {
    pub(crate) logic: ProofLogic,
    /// `declare-const*`, then asserts group by group (DAG-linear). No
    /// `set-logic` (the solver is built for `logic`).
    pub(crate) text: String,
    /// Asserts per group, in order.
    pub(crate) group_sizes: Vec<usize>,
    pub(crate) var_sorts: FxHashMap<String, ChcSort>,
    /// Recorded on the board (critique D2-yield M3).
    pub(crate) dag: DagStats,
}

/// What the fragment scan saw.
#[derive(Default)]
struct Fragment {
    var_sorts: FxHashMap<String, ChcSort>,
    int_vars: bool,
    real_vars: bool,
    real_consts: bool,
}

fn is_numeral(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Int(_) | ChcExpr::Real(..) => true,
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => is_numeral(&args[0]),
        _ => false,
    }
}

/// DAG-memoised scan of `roots` for the QF_LIA/QF_LRA(+Bool) fragment.
fn scan_fragment(roots: &[&ChcExpr], cap: usize) -> Result<Fragment, ItpUnknown> {
    let mut frag = Fragment::default();
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = roots.to_vec();
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(expr) as usize) {
            continue;
        }
        if seen.len() > cap {
            return Err(ItpUnknown::Size);
        }
        match expr {
            ChcExpr::ArrayLambda(_) => return Err(ItpUnknown::Fragment),
            ChcExpr::Bool(_) | ChcExpr::Int(_) => {}
            ChcExpr::Real(..) => frag.real_consts = true,
            ChcExpr::Var(v) => {
                match v.sort {
                    ChcSort::Int => frag.int_vars = true,
                    ChcSort::Real => frag.real_vars = true,
                    ChcSort::Bool => {}
                    _ => return Err(ItpUnknown::Fragment),
                }
                match frag.var_sorts.get(&v.name) {
                    Some(sort) if *sort != v.sort => return Err(ItpUnknown::Fragment),
                    Some(_) => {}
                    None => {
                        frag.var_sorts.insert(v.name.clone(), v.sort.clone());
                    }
                }
            }
            ChcExpr::Op(op, args) => {
                let supported = matches!(
                    op,
                    ChcOp::Not
                        | ChcOp::And
                        | ChcOp::Or
                        | ChcOp::Implies
                        | ChcOp::Iff
                        | ChcOp::Add
                        | ChcOp::Sub
                        | ChcOp::Mul
                        | ChcOp::Neg
                        | ChcOp::Eq
                        | ChcOp::Ne
                        | ChcOp::Lt
                        | ChcOp::Le
                        | ChcOp::Gt
                        | ChcOp::Ge
                        | ChcOp::Ite
                );
                if !supported {
                    return Err(ItpUnknown::Fragment);
                }
                // Linear arithmetic only: at most one non-numeral factor.
                if *op == ChcOp::Mul && args.iter().filter(|a| !is_numeral(a)).count() > 1 {
                    return Err(ItpUnknown::Fragment);
                }
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::BitVec(..)
            | ChcExpr::PredicateApp(..)
            | ChcExpr::FuncApp(..)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(..) => return Err(ItpUnknown::Fragment),
        }
    }
    Ok(frag)
}

/// Logic of a scanned fragment: Real vars (or Real constants without Int
/// vars) make it QF_LRA; Int vars QF_LIA; both is outside the fragment.
fn fragment_logic(frag: &Fragment) -> Result<ProofLogic, ItpUnknown> {
    match (frag.int_vars, frag.real_vars || frag.real_consts) {
        (true, true) => Err(ItpUnknown::Fragment),
        (false, true) => Ok(ProofLogic::QfLra),
        _ => Ok(ProofLogic::QfLia),
    }
}

/// Fragment logic of `roots` (DAG scan against `cap` unique nodes).
pub(crate) fn scan_logic(roots: &[&ChcExpr], cap: usize) -> Result<ProofLogic, ItpUnknown> {
    fragment_logic(&scan_fragment(roots, cap)?)
}

/// Build the script for `groups` (fragment gate + DAG-linear printing).
pub(crate) fn build_group_script(
    groups: &[&[ChcExpr]],
    caps: DagCaps,
) -> Result<GroupScript, ItpUnknown> {
    let roots: Vec<&ChcExpr> = groups.iter().flat_map(|g| g.iter()).collect();
    if roots.is_empty() {
        return Err(ItpUnknown::Fragment);
    }
    let frag = scan_fragment(&roots, caps.max_unique_nodes)?;
    let logic = fragment_logic(&frag)?;
    if frag.var_sorts.is_empty() {
        // Ground groups have nothing to interpolate over (the old gate's
        // `not_applicable_no_vars`).
        return Err(ItpUnknown::Fragment);
    }
    let mut names: Vec<&String> = frag.var_sorts.keys().collect();
    names.sort();
    let mut text = String::with_capacity(64 * names.len() + 1024);
    for name in names {
        text.push_str("(declare-const ");
        text.push_str(&quote_symbol(name));
        text.push(' ');
        text.push_str(&sort_to_smtlib(&frag.var_sorts[name]));
        text.push_str(")\n");
    }
    let dag = dag_smtlib::write_asserts_dag(&mut text, &roots, caps).map_err(|e| match e {
        dag_smtlib::DagError::UniqueNodeCap | dag_smtlib::DagError::DepthCap => ItpUnknown::Size,
        dag_smtlib::DagError::Unsupported(_) => ItpUnknown::Fragment,
    })?;
    Ok(GroupScript {
        logic,
        text,
        group_sizes: groups.iter().map(|g| g.len()).collect(),
        var_sorts: frag.var_sorts,
        dag,
    })
}

// ---------------------------------------------------------------------------
// ay-dpll Term -> ChcExpr (sort-preserving, fail-closed)
// ---------------------------------------------------------------------------

/// `BigRational` → `ChcExpr::Real(i64, i64)`, or `CoefficientOverflow`.
fn rational_to_real(r: &BigRational) -> Result<ChcExpr, ItpFail> {
    let n = r.numer().to_i64().ok_or(ItpFail::CoefficientOverflow)?;
    let d = r.denom().to_i64().ok_or(ItpFail::CoefficientOverflow)?;
    Ok(ChcExpr::Real(n, d))
}

/// Parse an unsigned decimal numeral or decimal literal (`N`, `N.M`).
fn parse_decimal(text: &str) -> Option<BigRational> {
    let t = text.trim();
    if let Some((int_part, frac)) = t.split_once('.') {
        if int_part.is_empty() || !int_part.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        if !frac.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let int: BigInt = int_part.parse().ok()?;
        if frac.is_empty() {
            return Some(BigRational::from_integer(int));
        }
        let scale = BigInt::from(10).pow(u32::try_from(frac.len()).ok()?);
        let frac: BigInt = frac.parse().ok()?;
        Some(BigRational::new(int * &scale + frac, scale))
    } else {
        if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        Some(BigRational::from_integer(t.parse().ok()?))
    }
}

/// Parse the value of a formatted ay-dpll numeral: `N`, `N.M`, `(- X)`,
/// `(/ X Y)` (X, Y themselves numerals, possibly `N.0`).
fn parse_rational_text(text: &str) -> Option<BigRational> {
    let t = text.trim();
    if let Some(inner) = t.strip_prefix("(-").and_then(|s| s.strip_suffix(')')) {
        return parse_rational_text(inner).map(|r| -r);
    }
    if let Some(inner) = t.strip_prefix("(/").and_then(|s| s.strip_suffix(')')) {
        let inner = inner.trim();
        // Split at the top level: the numerator may itself be parenthesised.
        let (num, den) = split_top_level_pair(inner)?;
        let num = parse_rational_text(num)?;
        let den = parse_rational_text(den)?;
        if den.is_zero() {
            return None;
        }
        return Some(num / den);
    }
    parse_decimal(t)
}

/// Split `"a b"` into its two top-level s-expressions.
fn split_top_level_pair(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            c if c.is_whitespace() && depth == 0 => {
                let (a, b) = s.split_at(i);
                let b = b.trim();
                if a.is_empty() || b.is_empty() {
                    return None;
                }
                return Some((a, b));
            }
            _ => {}
        }
    }
    None
}

/// Parse a formatted ay-dpll constant of the given sort (sort-preserving):
/// Bool `true`/`false`; Int `N` / `(- N)` → `ChcExpr::Int(i128)`; Real
/// `N.0`, `(- N.0)`, `(/ n d)`, `(- (/ n d))`, decimals → `ChcExpr::Real`.
/// A value outside `i128` / `(i64, i64)` is `CoefficientOverflow`.
pub(crate) fn parse_const_text(text: &str, sort: &ChcSort) -> Result<ChcExpr, ItpFail> {
    let t = text.trim();
    match sort {
        ChcSort::Bool => match t {
            "true" => Ok(ChcExpr::Bool(true)),
            "false" => Ok(ChcExpr::Bool(false)),
            _ => Err(ItpFail::Conversion),
        },
        ChcSort::Int => {
            let r = parse_rational_text(t).ok_or(ItpFail::Conversion)?;
            if !r.denom().is_one() {
                return Err(ItpFail::Conversion);
            }
            let n = r.numer().to_i128().ok_or(ItpFail::CoefficientOverflow)?;
            Ok(ChcExpr::Int(n))
        }
        ChcSort::Real => {
            let r = parse_rational_text(t).ok_or(ItpFail::Conversion)?;
            rational_to_real(&r)
        }
        _ => Err(ItpFail::Conversion),
    }
}

/// Value of a numeral `ChcExpr` (Int, Real, or a negated numeral).
fn numeral_value(expr: &ChcExpr) -> Option<BigRational> {
    match expr {
        ChcExpr::Int(n) => Some(BigRational::from_integer(BigInt::from(*n))),
        ChcExpr::Real(n, d) if *d != 0 => {
            Some(BigRational::new(BigInt::from(*n), BigInt::from(*d)))
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => numeral_value(&args[0]).map(|v| -v),
        _ => None,
    }
}

fn chc_sort_of(sort: &DpllSort) -> Option<ChcSort> {
    match sort {
        DpllSort::Bool => Some(ChcSort::Bool),
        DpllSort::Int => Some(ChcSort::Int),
        DpllSort::Real => Some(ChcSort::Real),
        _ => None,
    }
}

fn op(op: ChcOp, args: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(op, args))
}

/// Left-fold a binary operator over `args` (≥ 1 argument), sharing children.
fn fold_binary(o: ChcOp, args: Vec<Arc<ChcExpr>>) -> Result<Arc<ChcExpr>, ItpFail> {
    let mut it = args.into_iter();
    let mut acc = it.next().ok_or(ItpFail::Conversion)?;
    for next in it {
        acc = op(o, vec![acc, next]);
    }
    Ok(acc)
}

/// Build one converted application from its converted children.
fn app_to_chc(
    name: &str,
    args: Vec<Arc<ChcExpr>>,
    result_sort: &ChcSort,
) -> Result<Arc<ChcExpr>, ItpFail> {
    let pair = |args: Vec<Arc<ChcExpr>>| -> Result<(Arc<ChcExpr>, Arc<ChcExpr>), ItpFail> {
        let mut it = args.into_iter();
        match (it.next(), it.next(), it.next()) {
            (Some(a), Some(b), None) => Ok((a, b)),
            _ => Err(ItpFail::Conversion),
        }
    };
    Ok(match name {
        "and" | "or" => {
            let o = if name == "and" { ChcOp::And } else { ChcOp::Or };
            match args.len() {
                0 => Arc::new(ChcExpr::Bool(name == "and")),
                1 => args.into_iter().next().ok_or(ItpFail::Conversion)?,
                _ => op(o, args),
            }
        }
        "not" => {
            let mut it = args.into_iter();
            match (it.next(), it.next()) {
                (Some(a), None) => op(ChcOp::Not, vec![a]),
                _ => return Err(ItpFail::Conversion),
            }
        }
        "=>" => {
            let (a, b) = pair(args)?;
            op(ChcOp::Implies, vec![a, b])
        }
        "=" => {
            if args.len() < 2 {
                return Err(ItpFail::Conversion);
            }
            if args.len() == 2 {
                let (a, b) = pair(args)?;
                op(ChcOp::Eq, vec![a, b])
            } else {
                // Chainable `=`: conjunction of adjacent equalities.
                let eqs: Vec<Arc<ChcExpr>> = args
                    .windows(2)
                    .map(|w| op(ChcOp::Eq, vec![w[0].clone(), w[1].clone()]))
                    .collect();
                op(ChcOp::And, eqs)
            }
        }
        "distinct" => {
            let (a, b) = pair(args)?;
            op(ChcOp::Ne, vec![a, b])
        }
        "<" | "<=" | ">" | ">=" => {
            let o = match name {
                "<" => ChcOp::Lt,
                "<=" => ChcOp::Le,
                ">" => ChcOp::Gt,
                _ => ChcOp::Ge,
            };
            let (a, b) = pair(args)?;
            op(o, vec![a, b])
        }
        "+" => fold_binary(ChcOp::Add, args)?,
        "-" => {
            if args.len() == 1 {
                let a = args.into_iter().next().ok_or(ItpFail::Conversion)?;
                match numeral_value(&a) {
                    // Keep numerals as constants (sort-preserving).
                    Some(v) if matches!(result_sort, ChcSort::Real) => {
                        Arc::new(rational_to_real(&-v)?)
                    }
                    Some(v) if matches!(result_sort, ChcSort::Int) && v.denom().is_one() => {
                        let n = (-v).numer().to_i128().ok_or(ItpFail::CoefficientOverflow)?;
                        Arc::new(ChcExpr::Int(n))
                    }
                    _ => op(ChcOp::Neg, vec![a]),
                }
            } else {
                fold_binary(ChcOp::Sub, args)?
            }
        }
        "*" => {
            // Linear only: at most one non-numeral factor.
            if args.iter().filter(|a| numeral_value(a).is_none()).count() > 1 {
                return Err(ItpFail::Conversion);
            }
            fold_binary(ChcOp::Mul, args)?
        }
        "/" => {
            let (a, b) = pair(args)?;
            let (Some(n), Some(d)) = (numeral_value(&a), numeral_value(&b)) else {
                return Err(ItpFail::Conversion);
            };
            if d.is_zero() {
                return Err(ItpFail::Conversion);
            }
            Arc::new(rational_to_real(&(n / d))?)
        }
        "to_real" => {
            let mut it = args.into_iter();
            let (Some(a), None) = (it.next(), it.next()) else {
                return Err(ItpFail::Conversion);
            };
            let v = numeral_value(&a).ok_or(ItpFail::Conversion)?;
            Arc::new(rational_to_real(&v)?)
        }
        _ => return Err(ItpFail::Conversion),
    })
}

/// Sort-preserving; Real constants `N`, `(- N)`, `(/ N D)`, decimals; `/`
/// only const/const; `*` only with a constant side; a value outside
/// `ChcExpr::Real(i64,i64)` / `ChcExpr::Int(i128)` =>
/// `Err(ItpFail::CoefficientOverflow)`. Variables take their sort from
/// `sorts` (the script's declarations; an undeclared name is `Conversion`).
/// `budget` bounds the DISTINCT nodes converted (`Budget` when exhausted).
pub(crate) fn dpll_term_to_chc_expr(
    s: &Solver,
    t: DpllTerm,
    sorts: &FxHashMap<String, ChcSort>,
    budget: &mut usize,
) -> Result<ChcExpr, ItpFail> {
    let mut memo: FxHashMap<DpllTerm, Arc<ChcExpr>> = FxHashMap::default();
    let mut stack: Vec<(DpllTerm, bool)> = vec![(t, false)];
    while let Some((term, expanded)) = stack.pop() {
        if memo.contains_key(&term) {
            continue;
        }
        let kind = s.term_kind(term);
        let leaf = match &kind {
            TermKind::Var { name } => {
                let sort = sorts.get(name).ok_or(ItpFail::Conversion)?;
                Some(Arc::new(ChcExpr::Var(ChcVar::new(
                    name.clone(),
                    sort.clone(),
                ))))
            }
            TermKind::Const => {
                let sort = chc_sort_of(&s.term_sort(term)).ok_or(ItpFail::Conversion)?;
                Some(Arc::new(parse_const_text(&s.format_term(term), &sort)?))
            }
            TermKind::Forall | TermKind::Exists | TermKind::Let => {
                return Err(ItpFail::Conversion);
            }
            _ => None,
        };
        if let Some(leaf) = leaf {
            *budget = budget.checked_sub(1).ok_or(ItpFail::Budget)?;
            memo.insert(term, leaf);
            continue;
        }
        let children = s.term_children(term);
        if !expanded {
            stack.push((term, true));
            for &child in children.iter().rev() {
                if !memo.contains_key(&child) {
                    stack.push((child, false));
                }
            }
            continue;
        }
        *budget = budget.checked_sub(1).ok_or(ItpFail::Budget)?;
        let args: Vec<Arc<ChcExpr>> = children
            .iter()
            .map(|c| memo.get(c).cloned().ok_or(ItpFail::Conversion))
            .collect::<Result<_, _>>()?;
        let built = match kind {
            TermKind::Not => app_to_chc("not", args, &ChcSort::Bool)?,
            TermKind::Ite => {
                if args.len() != 3 {
                    return Err(ItpFail::Conversion);
                }
                op(ChcOp::Ite, args)
            }
            TermKind::App { name, .. } => {
                let sort = chc_sort_of(&s.term_sort(term)).ok_or(ItpFail::Conversion)?;
                app_to_chc(&name, args, &sort)?
            }
            _ => return Err(ItpFail::Conversion),
        };
        memo.insert(term, built);
    }
    memo.get(&t)
        .map(|root| (**root).clone())
        .ok_or(ItpFail::Conversion)
}

/// Distinct variable names of a (possibly DAG-shaped) expression, visiting
/// each node once (`ChcExpr::vars` walks the tree).
pub(crate) fn dag_var_names(expr: &ChcExpr) -> FxHashSet<String> {
    let mut out = FxHashSet::default();
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(e) as usize) {
            continue;
        }
        match e {
            ChcExpr::Var(v) => {
                out.insert(v.name.clone());
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(_, v) => stack.push(v.as_ref()),
            _ => {}
        }
    }
    out
}

/// Distinct nodes of a (possibly DAG-shaped) expression, up to `cap`.
pub(crate) fn dag_node_count(expr: &ChcExpr, cap: usize) -> usize {
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        if seen.len() >= cap {
            break;
        }
        if !seen.insert(std::ptr::from_ref(e) as usize) {
            continue;
        }
        if let ChcExpr::Op(_, args) = e {
            stack.extend(args.iter().map(AsRef::as_ref));
        }
    }
    seen.len()
}
