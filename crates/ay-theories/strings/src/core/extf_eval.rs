// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground term resolution and core extf predicate dispatch.
//!
//! Contains:
//! - Ground (EQC constant) string/integer term resolution
//! - Ground string/integer function reduction
//! - Core eval_extf_predicate dispatch (delegates to entailment methods)
//! - Recursive resolve_string_term with depth limiting
//!
//! Effort-1 (NF-derived) methods: see `extf_eval_effort1.rs`
//! Structural entailment: see `extf_eval_entailment.rs`

use super::*;

impl CoreSolver {
    /// Try to reduce a string function application to a concrete value.
    ///
    /// Unlike `resolve_string_term`, this only evaluates function applications
    /// (str.at, str.substr, str.replace, str.from_int, str.to_lower,
    /// str.to_upper) — not EQC constants or syntactic constants.
    pub(super) fn try_reduce_string_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.at" if args.len() == 2 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let i = Self::resolve_int_term(terms, state, args[1], 0)?;
                crate::eval::eval_str_at(&s, &i)
            }
            "str.substr" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let i = Self::resolve_int_term(terms, state, args[1], 0)?;
                let j = Self::resolve_int_term(terms, state, args[2], 0)?;
                crate::eval::eval_str_substr(&s, &i, &j)
            }
            "str.replace" if args.len() == 3 => {
                // Identity reduction: str.replace(s, s, u) = u for all s.
                // When haystack and pattern are in the same EQC, the result
                // is always the replacement string regardless of s's value.
                if state.find(args[0]) == state.find(args[1]) {
                    return Self::resolve_string_term(terms, state, args[2], 0);
                }
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t_str = Self::resolve_string_term(terms, state, args[1], 0)?;
                let u = Self::resolve_string_term(terms, state, args[2], 0)?;
                Some(crate::eval::eval_str_replace(&s, &t_str, &u))
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = Self::resolve_int_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_from_int(&n))
            }
            "str.replace_all" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t_str = Self::resolve_string_term(terms, state, args[1], 0)?;
                let u = Self::resolve_string_term(terms, state, args[2], 0)?;
                Some(crate::eval::eval_str_replace_all(&s, &t_str, &u))
            }
            "str.replace_re" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t = Self::resolve_string_term(terms, state, args[2], 0)?;
                Self::eval_str_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let t = Self::resolve_string_term(terms, state, args[2], 0)?;
                Self::eval_str_replace_re_all(terms, &s, args[1], &t)
            }
            "str.from_code" if args.len() == 1 => {
                let n = Self::resolve_int_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_from_code(&n))
            }
            "str.to_lower" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_lower(&s))
            }
            "str.to_upper" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_upper(&s))
            }
            _ => None,
        }
    }

    /// Try to reduce an integer-valued string function to a concrete BigInt.
    pub(super) fn try_reduce_int_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<BigInt> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.to_int" | "str.to.int" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_int(&s))
            }
            "str.indexof" if args.len() == 3 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                let pat = Self::resolve_string_term(terms, state, args[1], 0)?;
                let start = Self::resolve_int_term(terms, state, args[2], 0)?;
                crate::eval::eval_str_indexof(&s, &pat, &start)
            }
            // str.len is NOT evaluated here — it is handled by the LIA solver
            // and length axiom infrastructure. Evaluating str.len in the string
            // core solver can cause false conflicts when EQC constants are stale.
            "str.to_code" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(crate::eval::eval_str_to_code(&s))
            }
            _ => None,
        }
    }

    /// Evaluate supported extf predicates if their arguments resolve to strings.
    ///
    /// Returns `None` when the predicate is unsupported or any argument cannot
    /// be resolved to a concrete constant.
    pub(super) fn eval_extf_predicate(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                Self::eval_contains(terms, state, args[0], args[1])
            }
            "str.prefixof" if args.len() == 2 => {
                Self::eval_prefixof(terms, state, args[0], args[1])
            }
            "str.suffixof" if args.len() == 2 => {
                Self::eval_suffixof(terms, state, args[0], args[1])
            }
            "str.<=" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a <= b)
            }
            "str.<" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(false);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a < b)
            }
            "str.is_digit" if args.len() == 1 => {
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                // SMT-LIB: true iff s is a single character in '0'-'9'.
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Resolve a string term to a concrete string when possible.
    ///
    /// Resolution order:
    /// 1. EQC constant value
    /// 2. Syntactic string constant
    /// 3. Concat of recursively-resolved string terms
    /// 4. `str.at(s, i)` with resolved string and integer arguments
    /// 5. `str.substr(s, i, j)` with resolved arguments
    /// 6. `str.replace(s, t, u)` with resolved arguments
    pub(super) fn resolve_string_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        depth: usize,
    ) -> Option<String> {
        if depth > Self::MAX_RESOLVE_DEPTH {
            return None;
        }

        let rep = state.find(t);
        if let Some(s) = state.get_eqc(&rep).and_then(|e| e.constant.as_deref()) {
            if *DEBUG_STRING_CORE && depth == 0 && !matches!(terms.get(t), TermData::Const(_)) {
                eprintln!(
                    "[STRING_CORE] resolve_string_term: {t:?} (rep={rep:?}) -> EQC constant {s:?}"
                );
            }
            return Some(s.to_owned());
        }

        match terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            TermData::App(sym, args) => match sym.name() {
                "str.++" => {
                    let mut out = String::new();
                    for &arg in args {
                        out.push_str(&Self::resolve_string_term(terms, state, arg, depth + 1)?);
                    }
                    Some(out)
                }
                "str.at" if args.len() == 2 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let i = Self::resolve_int_term(terms, state, args[1], depth + 1)?;
                    crate::eval::eval_str_at(&s, &i)
                }
                "str.substr" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let i = Self::resolve_int_term(terms, state, args[1], depth + 1)?;
                    let j = Self::resolve_int_term(terms, state, args[2], depth + 1)?;
                    crate::eval::eval_str_substr(&s, &i, &j)
                }
                "str.replace" if args.len() == 3 => {
                    // Identity reduction: str.replace(s, s, u) = u for all s.
                    if state.find(args[0]) == state.find(args[1]) {
                        return Self::resolve_string_term(terms, state, args[2], depth + 1);
                    }
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t_str = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let u = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Some(crate::eval::eval_str_replace(&s, &t_str, &u))
                }
                "str.replace_all" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t_str = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let u = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Some(crate::eval::eval_str_replace_all(&s, &t_str, &u))
                }
                "str.replace_re" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_replace_re(terms, &s, args[1], &t)
                }
                "str.replace_re_all" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let t = Self::resolve_string_term(terms, state, args[2], depth + 1)?;
                    Self::eval_str_replace_re_all(terms, &s, args[1], &t)
                }
                "str.from_int" | "int.to.str" if args.len() == 1 => {
                    let n = Self::resolve_int_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_from_int(&n))
                }
                "str.from_code" if args.len() == 1 => {
                    let n = Self::resolve_int_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_from_code(&n))
                }
                "str.to_lower" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_lower(&s))
                }
                "str.to_upper" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_upper(&s))
                }
                _ => None,
            },
            _ => None,
        }
    }
}
