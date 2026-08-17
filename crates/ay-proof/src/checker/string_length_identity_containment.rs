// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Containment-bound recognition for string-length identity lemmas.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::{as_binary, str_len_arg};

// ---------------------------------------------------------------------------
// 6. Containment bound: contains/prefixof/suffixof → len(contained) <= len(container)
//    Stored as `(or (not PRED) (<= (str.len contained) (str.len container)))`.
// ---------------------------------------------------------------------------

pub(super) fn is_containment_len_bound(terms: &TermStore, t: TermId) -> bool {
    let TermData::App(Symbol::Named(sym), args) = terms.get(t) else {
        return false;
    };
    if sym != "or"
        || args.len() != 2
        || !matches!(terms.sort(t), Sort::Bool)
        || args
            .iter()
            .any(|&arg| !matches!(terms.sort(arg), Sort::Bool))
    {
        return false;
    }
    check_containment(terms, args[0], args[1]) || check_containment(terms, args[1], args[0])
}

fn check_containment(terms: &TermStore, neg_lit: TermId, le_lit: TermId) -> bool {
    let TermData::Not(pred) = terms.get(neg_lit) else {
        return false;
    };
    if !matches!(terms.sort(*pred), Sort::Bool) {
        return false;
    }
    let TermData::App(Symbol::Named(psym), pargs) = terms.get(*pred) else {
        return false;
    };
    if pargs.len() != 2
        || pargs
            .iter()
            .any(|&arg| !matches!(terms.sort(arg), Sort::String))
    {
        return false;
    }
    // (contained, container) per SMT-LIB argument order.
    let (contained, container) = match psym.as_str() {
        "str.contains" => (pargs[1], pargs[0]),
        "str.prefixof" | "str.suffixof" => (pargs[0], pargs[1]),
        _ => return false,
    };
    let Some((lo, hi)) = as_binary(terms, le_lit, "<=") else {
        return false;
    };
    str_len_arg(terms, lo) == Some(contained) && str_len_arg(terms, hi) == Some(container)
}
