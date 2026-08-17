// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic detection and sort-to-SMT-LIB conversion helpers for the executor adapter.

use crate::{ChcDtConstructor, ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Collect unique datatype declarations from a set of variables.
/// Returns a Vec of (name, constructors) pairs, deduplicated by name.
pub(crate) fn collect_dt_declarations(vars: &[ChcVar]) -> Vec<(&str, &[ChcDtConstructor])> {
    let mut seen = FxHashSet::default();
    let mut decls = Vec::new();
    for var in vars {
        collect_dt_from_sort(&var.sort, &mut seen, &mut decls);
    }
    decls
}

/// Collect unique datatype declarations from free variables and expression-local
/// constructor/selector/tester terms.
pub(crate) fn collect_dt_declarations_for_expr<'a>(
    vars: &'a [ChcVar],
    expr: &'a ChcExpr,
) -> Vec<(&'a str, &'a [ChcDtConstructor])> {
    let mut seen = FxHashSet::default();
    let mut decls = Vec::new();
    for var in vars {
        collect_dt_from_sort(&var.sort, &mut seen, &mut decls);
    }
    collect_dt_from_expr(expr, &mut seen, &mut decls);
    decls
}

/// Recursively collect DT declarations from a sort (handles Array(DT, DT), nested DTs).
fn collect_dt_from_sort<'a>(
    sort: &'a ChcSort,
    seen: &mut FxHashSet<&'a str>,
    decls: &mut Vec<(&'a str, &'a [ChcDtConstructor])>,
) {
    match sort {
        ChcSort::Datatype { name, constructors } if seen.insert(name.as_str()) => {
            decls.push((name.as_str(), constructors.as_slice()));
            // Also collect DTs used in selector sorts (nested DTs).
            for ctor in constructors.iter() {
                for sel in &ctor.selectors {
                    collect_dt_from_sort(&sel.sort, seen, decls);
                }
            }
        }
        ChcSort::Array(k, v) => {
            collect_dt_from_sort(k, seen, decls);
            collect_dt_from_sort(v, seen, decls);
        }
        _ => {}
    }
}

fn collect_dt_from_expr<'a>(
    expr: &'a ChcExpr,
    seen: &mut FxHashSet<&'a str>,
    decls: &mut Vec<(&'a str, &'a [ChcDtConstructor])>,
) {
    match expr {
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::IsTesterMarker(_) => {}
        ChcExpr::Var(var) => collect_dt_from_sort(&var.sort, seen, decls),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            for arg in args {
                collect_dt_from_expr(arg, seen, decls);
            }
        }
        ChcExpr::FuncApp(_, sort, args) => {
            collect_dt_from_sort(sort, seen, decls);
            for arg in args {
                collect_dt_from_expr(arg, seen, decls);
            }
        }
        ChcExpr::ConstArrayMarker(sort) => collect_dt_from_sort(sort, seen, decls),
        ChcExpr::ConstArray(key_sort, value) => {
            collect_dt_from_sort(key_sort, seen, decls);
            collect_dt_from_expr(value, seen, decls);
        }
    }
}

/// Emit a `(declare-datatype Name ((ctor1 (sel1 Sort1) ...) ...))` command.
pub(crate) fn emit_declare_datatype(name: &str, ctors: &[ChcDtConstructor]) -> String {
    let mut s = String::new();
    s.push_str(&format!("(declare-datatype {} (", quote_symbol(name)));
    for ctor in ctors {
        s.push('(');
        s.push_str(&quote_symbol(&ctor.name));
        for sel in &ctor.selectors {
            s.push_str(&format!(
                " ({} {})",
                quote_symbol(&sel.name),
                sort_to_smtlib(&sel.sort)
            ));
        }
        s.push(')');
    }
    s.push_str("))\n");
    s
}

/// Detect the SMT-LIB logic string based on the sorts used in the formula.
pub(crate) fn detect_logic(vars: &[ChcVar], expr: &ChcExpr) -> &'static str {
    let expr_features = expr.scan_features();
    let mut has_array = vars.iter().any(|v| sort_contains_array(&v.sort))
        || expr.contains_array_ops()
        || expr_sort_has(expr, sort_contains_array);
    // Check sorts including nested array element/index sorts (#7024) and
    // recursively nested DT selector fields (#7016). Cycle guards prevent
    // self-recursive datatypes from recursing forever.
    let has_bv = vars.iter().any(|v| sort_contains_bv(&v.sort))
        || expr_features.has_bv
        || expr_sort_has(expr, sort_contains_bv);
    let has_int =
        vars.iter().any(|v| sort_contains_int(&v.sort)) || expr_sort_has(expr, sort_contains_int);
    let has_real =
        vars.iter().any(|v| sort_contains_real(&v.sort)) || expr_sort_has(expr, sort_contains_real);
    let has_dt = vars.iter().any(|v| sort_contains_dt(&v.sort))
        || expr_features.has_dt
        || expr_sort_has(expr, sort_contains_dt);
    let has_nonlinear_mul = expr.contains_nonlinear_mul();
    if has_dt {
        has_array |= vars.iter().any(|v| sort_contains_array(&v.sort))
            || expr_sort_has(expr, sort_contains_array);
    }

    // BITVECTORS MIXED WITH INT/REAL MUST NOT TAKE A BV-ONLY FAMILY NAME.
    //
    // Every QF_*BV and _DT_*BV label routes the query to an eager bit-blast
    // pipeline that carries no integer or real theory.  Let the executor's
    // content-driven `ALL` route select its conservative BV/arithmetic lane;
    // it keeps independent BV and arithmetic constraints soundly separated
    // and fails closed when conversion operators couple the theories.
    //
    // Datatypes make this combination stricter: the executor has no combined
    // DT+BV+arithmetic solver.  Use one of its explicitly recognized,
    // fail-closed combined tokens so dispatch returns `unknown` instead of
    // selecting either `_DT_AUFBV` (drops arithmetic) or `_DT_AUFLI*` (drops
    // bit-vector semantics).  The non-DT case can use content-driven `ALL`,
    // which selects the existing independent/coupled BV-arithmetic lanes.
    if has_bv && (has_int || has_real) {
        if has_dt {
            return if has_real {
                "QF_AUFBVLIRA"
            } else {
                "QF_AUFBVLIA"
            };
        }
        return "ALL";
    }

    if has_dt {
        return match (has_array, has_bv, has_int, has_real) {
            (_, true, _, _) => "_DT_AUFBV",
            (true, _, _, true) => "_DT_AUFLIRA",
            (true, _, _, _) | (_, _, true, _) => "_DT_AUFLIA",
            (_, _, _, true) => "_DT_AUFLRA",
            _ => "QF_DT",
        };
    }

    if has_nonlinear_mul && !has_bv {
        match (has_array, has_int, has_real) {
            (true, true, true) => return "QF_AUFNIRA",
            (true, true, false) => return "QF_AUFNIA",
            (true, false, true) => return "QF_AUFNRA",
            (false, true, true) => return "QF_NIRA",
            (false, true, false) => return "QF_NIA",
            (false, false, true) => return "QF_NRA",
            _ => {}
        }
    }

    // BITVECTORS MIXED WITH INT/REAL MUST NOT TAKE A BV-FAMILY NAME.
    //
    // Every QF_*BV label routes the query to the eager bit-blast pipeline, which
    // carries no integer theory, so Int-sorted variables come back with NO
    // assignment. Model completion fills them with the sort default (0), and
    // validation then correctly reports the original Int assertion violated —
    // the solve degrades to `unknown (:reason-unknown incomplete)` rather than
    // `sat`. `has_int` was previously a don't-care in both BV arms, which is
    // exactly how a formula full of Int arithmetic acquired a BV logic name.
    //
    // MEASURED: an identical five-line query is `unknown` + MODEL-UNCONFIRMED
    // under QF_AUFBV and `sat` under ALL. Across one workspace this produced
    // ~59,896 MODEL-UNCONFIRMED events.
    //
    // SOUNDNESS: `ALL` only WIDENS the admissible theory set; it never changes a
    // formula's models, so it cannot turn a violation into UNSAT. It can only
    // let a query be decided that was previously abandoned.
    if has_bv && (has_int || has_real) {
        return "ALL";
    }

    match (has_array, has_bv, has_int, has_real) {
        (true, true, _, _) => "QF_AUFBV",
        (true, _, true, true) => "QF_AUFLIRA",
        (true, _, _, true) => "QF_AUFLRA",
        (true, _, true, _) => "QF_AUFLIA",
        (true, _, _, _) => "QF_AX",
        (false, true, _, _) => "QF_UFBV",
        _ => "QF_AUFLIA",
    }
}

fn expr_sort_has(expr: &ChcExpr, pred: fn(&ChcSort) -> bool) -> bool {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => false,
        ChcExpr::Var(var) => pred(&var.sort),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|arg| expr_sort_has(arg, pred))
        }
        ChcExpr::FuncApp(_, sort, args) => {
            pred(sort) || args.iter().any(|arg| expr_sort_has(arg, pred))
        }
        ChcExpr::ConstArrayMarker(sort) => pred(sort),
        ChcExpr::IsTesterMarker(_) => false,
        ChcExpr::ConstArray(key_sort, value) => pred(key_sort) || expr_sort_has(value, pred),
    }
}

/// Check if a sort (recursively) contains Int (#7024).
fn sort_contains_int(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Int => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains Real (#7024).
fn sort_contains_real(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Real => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains BitVec (#7024).
fn sort_contains_bv(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::BitVec(_) => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains datatypes (#7016).
fn sort_contains_dt(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Datatype { .. } => true,
        ChcSort::Array(idx, elem) => sort_contains_dt(idx) || sort_contains_dt(elem),
        _ => false,
    }
}

/// Check if a sort (recursively) contains arrays.
fn sort_contains_array(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Array(_, _) => true,
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Convert ChcSort to SMT-LIB sort string.
pub(crate) fn sort_to_smtlib(sort: &ChcSort) -> String {
    match sort {
        ChcSort::Bool => "Bool".to_string(),
        ChcSort::Int => "Int".to_string(),
        ChcSort::Real => "Real".to_string(),
        ChcSort::BitVec(w) => format!("(_ BitVec {w})"),
        ChcSort::Array(k, v) => format!("(Array {} {})", sort_to_smtlib(k), sort_to_smtlib(v)),
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => quote_symbol(name),
    }
}

/// Quote an SMT-LIB symbol if it contains special characters.
///
/// Delegates to `ay_core::quote_symbol` for correct handling of reserved
/// words (true, false, let, assert, ...) and pipe/backslash sanitization.
pub(crate) fn quote_symbol(name: &str) -> String {
    ay_core::quote_symbol(name)
}
