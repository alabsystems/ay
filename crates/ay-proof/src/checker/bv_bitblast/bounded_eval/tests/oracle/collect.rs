// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::collections::HashSet;

pub(super) fn collect_bounded_vars(terms: &TermStore, clause: &[TermId]) -> Option<Vec<EvalVar>> {
    let mut vars = Vec::new();
    let mut visited = HashSet::new();
    for &lit in clause {
        bounded_term(terms, lit, &mut vars, &mut visited, &mut Vec::new())?;
    }
    Some(vars)
}

fn bounded_term(
    terms: &TermStore,
    term: TermId,
    vars: &mut Vec<EvalVar>,
    visited: &mut HashSet<TermId>,
    stack: &mut Vec<TermId>,
) -> Option<()> {
    if stack.len() > 512 {
        return None;
    }
    if matches!(terms.sort(term), Sort::BitVec(bv) if bv.width > MAX_EVALUATED_BV_WIDTH) {
        return None;
    }
    if !visited.insert(term) {
        return Some(());
    }
    stack.push(term);
    let result = match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => Some(()),
        TermData::Const(Constant::BitVec { width, .. }) if *width <= MAX_EVALUATED_BV_WIDTH => {
            Some(())
        }
        TermData::Const(_) => None,
        TermData::Var(_, _) => {
            let (kind, bits) = match terms.sort(term) {
                Sort::Bool => (EvalVarKind::Bool, 1),
                Sort::BitVec(bv) if bv.width <= MAX_BOUNDED_BV_WIDTH => {
                    (EvalVarKind::BitVec, bv.width)
                }
                _ => return None,
            };
            vars.push(EvalVar { term, kind, bits });
            Some(())
        }
        TermData::App(sym, args) if supports_bounded_app(sym.name()) => {
            for &arg in args {
                bounded_term(terms, arg, vars, visited, stack)?;
            }
            Some(())
        }
        TermData::Not(inner) => bounded_term(terms, *inner, vars, visited, stack),
        TermData::Ite(c, t, e) => {
            bounded_term(terms, *c, vars, visited, stack)?;
            bounded_term(terms, *t, vars, visited, stack)?;
            bounded_term(terms, *e, vars, visited, stack)
        }
        _ => None,
    };
    stack.pop();
    result
}

fn supports_bounded_app(name: &str) -> bool {
    matches!(
        name,
        "=" | "or"
            | "and"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvnot"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvneg"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "concat"
            | "extract"
            | "zero_extend"
            | "sign_extend"
            | "rotate_left"
            | "rotate_right"
            | "repeat"
    )
}
