// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in term analysis recursion (#8414).
///
/// Logic detection functions recurse into term structure. On DT-heavy problems
/// with deeply nested terms, this can overflow the thread stack.
pub(super) const TERM_ANALYSIS_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for term analysis recursion.
pub(super) const TERM_ANALYSIS_STACK_SIZE: usize = 1024 * 1024;

/// Check if a term is a "pure arithmetic" term that LIA can represent.
///
/// Returns true if the term is:
/// - An integer/rational constant
/// - A variable of Int/Real sort
/// - An arithmetic operation (+, -, *, /) applied to pure arithmetic terms
///
/// Returns false if the term contains uninterpreted function applications.
pub(crate) fn is_pure_arithmetic_term(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
            TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int | Sort::Real),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" | "-" | "*" | "/" | "to_real" | "to_int" | "div" | "mod" | "abs" => {
                    args.iter().all(|&arg| is_pure_arithmetic_term(terms, arg))
                }
                _ => false,
            },
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check if a term is LIA-relevant for equality routing (#5041).
///
/// A term is LIA-relevant when the arithmetic solver can represent it, treating
/// any Int-sorted `select` (an array/LIA interface term) as an atomic leaf, just
/// like a plain Int variable. This mirrors [`is_pure_arithmetic_term`] exactly but
/// additionally admits Int selects as leaves.
///
/// Without recursing through arithmetic operators, an atom like
/// `(= (select u 3) (+ (select u 4) 2))` was misclassified as non-LIA (because the
/// RHS `(+ (select u 4) 2)` is neither pure-arithmetic nor a bare select), so the
/// equality — and, crucially, its negation — was never routed to LIA. That made
/// `ay` return `unknown` on trivially-UNSAT ground QF_AUFLIA goals such as
/// `select(u,3)=11, select(u,4)=9, ¬(select(u,3)=select(u,4)+2)`: LIA never saw the
/// disequality over the (already-shared) select terms it needed to refute it.
/// deductive-checks encodes sequences/multisets/sets/maps as arrays, so arithmetic over
/// select results (`len+1`, `count1+count2`, `a[i]+1`, …) is pervasive in its VCs.
///
/// Treating `select` as a leaf under the same operator set as
/// `is_pure_arithmetic_term` keeps behavior consistent with how arithmetic over
/// plain Int variables (including products) is already routed, so it only widens
/// routing to the arithmetic solver and never changes a sound verdict.
pub(super) fn is_lia_relevant_term(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
            TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int | Sort::Real),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                // Int-sorted array read: an array/LIA interface leaf.
                "select" if matches!(terms.sort(term), Sort::Int) => true,
                // Same arithmetic operator set as is_pure_arithmetic_term, but the
                // operands may themselves contain selects.
                "+" | "-" | "*" | "/" | "to_real" | "to_int" | "div" | "mod" | "abs" => {
                    args.iter().all(|&arg| is_lia_relevant_term(terms, arg))
                }
                _ => false,
            },
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check whether a term should be routed to arithmetic solvers.
pub(crate) fn contains_arithmetic_ops(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
                    return true;
                }
                if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                    return true;
                }
                if name == "=" && args.len() == 2 {
                    return is_lia_relevant_term(terms, args[0])
                        && is_lia_relevant_term(terms, args[1]);
                }
                if name == "distinct" && args.iter().all(|&arg| is_lia_relevant_term(terms, arg)) {
                    return true;
                }
                false
            }
            TermData::Not(inner) => contains_arithmetic_ops(terms, *inner),
            TermData::Ite(_, t, e) => {
                contains_arithmetic_ops(terms, *t) || contains_arithmetic_ops(terms, *e)
            }
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check if a term contains string-int bridge operations that require LIA.
pub(crate) fn contains_string_ops(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if matches!(
                    name.as_str(),
                    "str.len"
                        | "str.indexof"
                        | "str.to_int"
                        | "str.to.int"
                        | "str.from_int"
                        | "int.to.str"
                        | "str.replace"
                        | "str.replace_all"
                        | "str.substr"
                ) {
                    return true;
                }
                if matches!(name.as_str(), "str.to_code" | "str.from_code") {
                    return !is_ground_term(terms, term);
                }
                if matches!(
                    name.as_str(),
                    "str.contains" | "str.prefixof" | "str.suffixof"
                ) && !is_ground_term(terms, term)
                {
                    return true;
                }
                if name == "="
                    && args.len() == 2
                    && matches!(terms.sort(args[0]), Sort::String)
                    && (is_absorbing_concat_eq(terms, args[0], args[1])
                        || is_absorbing_concat_eq(terms, args[1], args[0]))
                {
                    return true;
                }
                args.iter().any(|&arg| contains_string_ops(terms, arg))
            }
            TermData::Not(inner) => contains_string_ops(terms, *inner),
            TermData::Ite(c, t, e) => {
                contains_string_ops(terms, *c)
                    || contains_string_ops(terms, *t)
                    || contains_string_ops(terms, *e)
            }
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check if a term contains seq-int bridge operations that require LIA.
pub(crate) fn contains_seq_len_ops(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "seq.len" {
                    return true;
                }
                if name == "=" && args.len() == 2 {
                    return contains_seq_len_ops(terms, args[0])
                        || contains_seq_len_ops(terms, args[1]);
                }
                if matches!(
                    name.as_str(),
                    "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/" | "div" | "mod" | "abs"
                ) {
                    return args.iter().any(|&arg| contains_seq_len_ops(terms, arg));
                }
                false
            }
            TermData::Not(inner) => contains_seq_len_ops(terms, *inner),
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check if `lhs = rhs` is an absorbing concat equation where `lhs` appears
/// inside a `str.++` on the `rhs` side.
pub(super) fn is_absorbing_concat_eq(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    if matches!(terms.get(lhs), TermData::Const(_)) {
        return false;
    }
    match terms.get(rhs) {
        TermData::App(Symbol::Named(name), args) if name == "str.++" => args
            .iter()
            .any(|&arg| arg == lhs || is_absorbing_concat_eq(terms, lhs, arg)),
        _ => false,
    }
}

/// Check whether a term is ground (contains no free variables).
///
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(super) fn is_ground_term(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::Var(..) | TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                false
            }
            TermData::Const(_) => true,
            TermData::App(_, args) => args.iter().all(|&arg| is_ground_term(terms, arg)),
            TermData::Not(inner) => is_ground_term(terms, *inner),
            TermData::Ite(c, t, e) => [*c, *t, *e].into_iter().all(|id| is_ground_term(terms, id)),
            other => unreachable!("unhandled TermData variant in is_ground_term(): {other:?}"),
        },
    ) // stacker::maybe_grow
}

/// Check if a literal could affect the array sub-solver's state.
pub(crate) fn involves_array(terms: &TermStore, term: TermId) -> bool {
    let inner = match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    };
    if matches!(terms.sort(inner), Sort::Array(_)) {
        return true;
    }
    match terms.get(inner) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "select" | "store" => true,
            "=" | "distinct" => true,
            _ => args
                .iter()
                .any(|&arg| matches!(terms.sort(arg), Sort::Array(_))),
        },
        _ => false,
    }
}

/// Check if a term involves Int-sorted arithmetic operands.
pub(crate) fn involves_int_arithmetic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2 {
                return matches!(terms.sort(args[0]), Sort::Int)
                    || matches!(terms.sort(args[1]), Sort::Int);
            }
            if name == "=" && args.len() == 2 {
                let has_int = matches!(terms.sort(args[0]), Sort::Int)
                    || matches!(terms.sort(args[1]), Sort::Int);
                if !has_int {
                    return false;
                }
                return is_lia_relevant_term(terms, args[0])
                    && is_lia_relevant_term(terms, args[1]);
            }
            if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                return matches!(terms.sort(term), Sort::Int);
            }
            if name == "distinct" {
                let has_int = args.iter().any(|&arg| matches!(terms.sort(arg), Sort::Int));
                let all_pure = args.iter().all(|&arg| is_lia_relevant_term(terms, arg));
                return has_int && all_pure;
            }
            false
        }
        TermData::Const(Constant::Int(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int),
        TermData::Not(inner) => involves_int_arithmetic(terms, *inner),
        _ => false,
    }
}

/// Check if ANY assertion contains substantive integer arithmetic constraints.
///
/// #8596: Also detects Int-sorted equalities involving array selects and
/// integer constants. When `(= (select a y) 1)` appears alongside
/// `(= a (store const_0 x 1))`, the Nelson-Oppen combination needs LIA
/// to discover model equalities (e.g., x = y). Without this, the AUFLIA
/// path fast-paths to ArrayEUF which has no LIA solver and cannot request
/// model equalities for Int-sorted index variables.
/// True when the assertion window's ONLY integer content is bare constants
/// and equalities/disequalities — no comparisons, no arithmetic operators, no
/// Int-sorted `distinct` (#qf-auflia-arrayeuf-retry). On this fragment the
/// Array+EUF solver is sound standalone: distinct Int constants are distinct
/// EUF atoms, UNSAT derivations (congruence + ROW) are valid under the Int
/// interpretation, and SAT verdicts still pass the fail-closed model gates.
pub(crate) fn int_constraints_are_constants_only(terms: &TermStore, assertions: &[TermId]) -> bool {
    fn bad(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        stacker::maybe_grow(
            TERM_ANALYSIS_STACK_RED_ZONE,
            TERM_ANALYSIS_STACK_SIZE,
            || {
                match terms.get(term) {
                    TermData::App(Symbol::Named(name), args) => {
                        if matches!(name.as_str(), "<" | "<=" | ">" | ">=")
                            && args
                                .iter()
                                .any(|&a| matches!(terms.sort(a), Sort::Int | Sort::Real))
                        {
                            return true;
                        }
                        if matches!(
                            name.as_str(),
                            "+" | "-"
                                | "*"
                                | "/"
                                | "mod"
                                | "div"
                                | "rem"
                                | "abs"
                                | "to_int"
                                | "to_real"
                        ) {
                            return true;
                        }
                        // `distinct` over Int is native EUF semantics (pairwise
                        // disequalities; Int's infinite domain never forces a
                        // collision), so it does NOT disqualify the fragment.
                        args.iter().any(|&a| bad(terms, a, visited))
                    }
                    TermData::App(_, args) => args.iter().any(|&a| bad(terms, a, visited)),
                    TermData::Not(inner) => bad(terms, *inner, visited),
                    TermData::Ite(c, t, e) => {
                        bad(terms, *c, visited)
                            || bad(terms, *t, visited)
                            || bad(terms, *e, visited)
                    }
                    _ => false,
                }
            },
        )
    }
    let mut visited = HashSet::default();
    !assertions.iter().any(|&a| bad(terms, a, &mut visited))
}

pub(crate) fn has_substantive_int_constraints(terms: &TermStore, assertions: &[TermId]) -> bool {
    fn check_term(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        stacker::maybe_grow(
            TERM_ANALYSIS_STACK_RED_ZONE,
            TERM_ANALYSIS_STACK_SIZE,
            || {
                match terms.get(term) {
                    TermData::App(Symbol::Named(name), args) => {
                        if matches!(name.as_str(), "<" | "<=" | ">" | ">=")
                            && args.len() == 2
                            && (matches!(terms.sort(args[0]), Sort::Int)
                                || matches!(terms.sort(args[1]), Sort::Int))
                        {
                            return true;
                        }
                        if matches!(
                            name.as_str(),
                            "+" | "-" | "*" | "/" | "mod" | "div" | "rem" | "abs"
                        ) && matches!(terms.sort(term), Sort::Int)
                        {
                            return true;
                        }
                        if name == "distinct"
                            && args.iter().any(|&arg| matches!(terms.sort(arg), Sort::Int))
                        {
                            return true;
                        }
                        // #8596: Detect Int-sorted equalities where one side involves
                        // an array select and the other is an integer constant (or vice
                        // versa). Pattern: `(= (select a y) 1)`. The integer constant
                        // constrains the array value, which in turn constrains array
                        // index equalities via ROW axioms. The LIA solver is needed for
                        // Nelson-Oppen model equality discovery on the index variables.
                        if name == "=" && args.len() == 2 {
                            let lhs_is_int_const =
                                matches!(terms.get(args[0]), TermData::Const(Constant::Int(_)));
                            let rhs_is_int_const =
                                matches!(terms.get(args[1]), TermData::Const(Constant::Int(_)));
                            if args
                                .iter()
                                .any(|&arg| is_int_uf_app_with_array_arg(terms, arg))
                            {
                                return true;
                            }
                            if (lhs_is_int_const || rhs_is_int_const)
                                && (matches!(terms.sort(args[0]), Sort::Int)
                                    || matches!(terms.sort(args[1]), Sort::Int))
                            {
                                let non_const_side =
                                    if lhs_is_int_const { args[1] } else { args[0] };
                                if involves_array_select(terms, non_const_side) {
                                    return true;
                                }
                            }
                        }
                        args.iter().any(|&arg| check_term(terms, arg, visited))
                    }
                    TermData::Const(Constant::Int(_)) => false,
                    TermData::Not(inner) => check_term(terms, *inner, visited),
                    TermData::Ite(c, t, e) => {
                        check_term(terms, *c, visited)
                            || check_term(terms, *t, visited)
                            || check_term(terms, *e, visited)
                    }
                    _ => false,
                }
            }, // stacker::maybe_grow
        )
    }

    let mut visited = HashSet::default();
    assertions
        .iter()
        .any(|&a| check_term(terms, a, &mut visited))
}

/// Check for Int-valued UF applications over array terms.
///
/// These terms are Skolem-style array witnesses in QF_AUFLIA. Routing them to
/// pure ArrayEUF leaves their integer value unconstrained by arithmetic model
/// equalities, so store/select disequality targets can stop at Unknown.
fn is_int_uf_app_with_array_arg(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::App(Symbol::Named(name), args)
                if !matches!(
                    name.as_str(),
                    "=" | "select"
                        | "store"
                        | "+"
                        | "-"
                        | "*"
                        | "/"
                        | "mod"
                        | "div"
                        | "rem"
                        | "abs"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                ) && matches!(terms.sort(term), Sort::Int) =>
            {
                args.iter()
                    .any(|&arg| matches!(terms.sort(arg), Sort::Array(_)))
            }
            _ => false,
        },
    )
}

/// Check if a term is or contains an array select expression.
///
/// Used by #8596 to detect `(= (select a y) 1)` patterns where the
/// select value constrains array index equalities.
fn involves_array_select(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || {
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "select" {
                        return true;
                    }
                    // Check if any subterm involves a select (e.g., `(+ (select a x) 1)`)
                    args.iter().any(|&arg| involves_array_select(terms, arg))
                }
                _ => false,
            }
        },
    )
}

/// Check if a term is LRA-relevant for equality routing (#5041).
pub(super) fn is_lra_relevant_term(terms: &TermStore, term: TermId) -> bool {
    if is_pure_arithmetic_term(terms, term) {
        return true;
    }
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if name == "select" && matches!(terms.sort(term), Sort::Real) {
            return true;
        }
        if name == "to_real" && args.len() == 1 {
            if let TermData::App(Symbol::Named(inner_name), _) = terms.get(args[0]) {
                if inner_name == "select" {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if a term involves Real-sorted arithmetic operands.
pub(crate) fn involves_real_arithmetic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2 {
                return matches!(terms.sort(args[0]), Sort::Real)
                    || matches!(terms.sort(args[1]), Sort::Real);
            }
            if name == "=" && args.len() == 2 {
                let has_real = matches!(terms.sort(args[0]), Sort::Real)
                    || matches!(terms.sort(args[1]), Sort::Real);
                if !has_real {
                    return false;
                }
                return is_lra_relevant_term(terms, args[0])
                    && is_lra_relevant_term(terms, args[1]);
            }
            if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                return matches!(terms.sort(term), Sort::Real);
            }
            if name == "distinct" {
                let has_real = args
                    .iter()
                    .any(|&arg| matches!(terms.sort(arg), Sort::Real));
                let all_relevant = args.iter().all(|&arg| is_lra_relevant_term(terms, arg));
                return has_real && all_relevant;
            }
            false
        }
        TermData::Const(Constant::Rational(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Real),
        TermData::Not(inner) => involves_real_arithmetic(terms, *inner),
        _ => false,
    }
}

/// Check if a term has arithmetic structure (contains +, -, *, / operations).
pub(super) fn has_arithmetic_structure(terms: &TermStore, term: TermId) -> bool {
    stacker::maybe_grow(
        TERM_ANALYSIS_STACK_RED_ZONE,
        TERM_ANALYSIS_STACK_SIZE,
        || match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" | "-" | "*" | "/" | "div" | "mod" => true,
                _ => args.iter().any(|&a| has_arithmetic_structure(terms, a)),
            },
            _ => false,
        },
    ) // stacker::maybe_grow
}

/// Check if a term is a `select` or `store` application.
pub(crate) fn is_select_or_store(terms: &TermStore, term: TermId) -> bool {
    if let TermData::App(ref sym, _) = terms.get(term) {
        let name = sym.name();
        name == "select" || name == "store"
    } else {
        false
    }
}

/// Check if a comparison atom's argument involves select/store terms.
pub(crate) fn arg_involves_select_or_store(terms: &TermStore, arg: TermId) -> bool {
    if is_select_or_store(terms, arg) {
        return true;
    }
    if let TermData::App(ref sym, ref inner_args) = terms.get(arg) {
        let name = sym.name();
        if name == "+" || name == "-" || name == "*" {
            return inner_args.iter().any(|&a| is_select_or_store(terms, a));
        }
    }
    false
}
