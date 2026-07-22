// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Effort-1 (NF-derived) evaluation and resolution for string/integer terms.
//!
//! These methods use normal-form data in addition to ground EQC constants,
//! enabling deeper evaluation at the cost of potential transient values.
//! Extracted from extf_eval.rs as part of #5970 code-health splits.

use super::*;

impl CoreSolver {
    /// Evaluate extf predicates using NF-derived substitutions.
    pub(super) fn eval_extf_predicate_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                // Soundness guard (#4057): avoid NF-only contains evaluation.
                //
                // Effort-1 NF substitutions can transiently resolve both sides
                // of a branch-local contains atom to constants. For reduction
                // guards (especially inside replace ITE branches), using those
                // transient values for hard conflicts can over-prune the search.
                //
                // Keep contains evaluation here strictly ground via direct EQC
                // constants/functions. Non-ground cases remain deferred.
                let h = Self::resolve_string_term(terms, state, args[0], 0)?;
                let n = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(h.contains(n.as_str()))
            }
            "str.prefixof" if args.len() == 2 => {
                // Soundness guard (#6309): use ground-only resolution, matching
                // the str.contains guard (#4057). NF-derived constants can
                // produce transient mismatches that cause false-UNSAT.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let prefix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.starts_with(prefix.as_str()))
            }
            "str.suffixof" if args.len() == 2 => {
                // Soundness guard (#6309): use ground-only resolution, matching
                // the str.contains guard (#4057).
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let suffix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.ends_with(suffix.as_str()))
            }
            "str.<=" if args.len() == 2 => {
                // Soundness guard (#6309): ground-only resolution.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a <= b)
            }
            "str.<" if args.len() == 2 => {
                // Soundness guard (#6309): ground-only resolution.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(false);
                }
                let a = Self::resolve_string_term(terms, state, args[0], 0)?;
                let b = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(a < b)
            }
            "str.is_digit" if args.len() == 1 => {
                // Soundness guard (#6309): ground-only resolution.
                let s = Self::resolve_string_term(terms, state, args[0], 0)?;
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Evaluate extf predicates using ground-only (EQC constant) resolution.
    /// Returns None if the predicate cannot be evaluated from ground data alone.
    /// Used to distinguish ground vs NF-derived conflicts (#6309).
    pub(super) fn eval_extf_predicate_ground(
        &self,
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };

        match sym.name() {
            "str.contains" if args.len() == 2 => {
                // Reflexivity: a string contains itself, so `contains(h, n)` holds
                // (ground-provably) whenever h and n are in the same EQC — needed so
                // the ground evaluator reproduces the `(not (str.contains x x))`
                // self-tautology conflict instead of failing closed.
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let h = Self::resolve_string_term(terms, state, args[0], 0)?;
                let n = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(h.contains(n.as_str()))
            }
            "str.prefixof" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let prefix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.starts_with(prefix.as_str()))
            }
            "str.suffixof" if args.len() == 2 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return Some(true);
                }
                let suffix = Self::resolve_string_term(terms, state, args[0], 0)?;
                let s = Self::resolve_string_term(terms, state, args[1], 0)?;
                Some(s.ends_with(suffix.as_str()))
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
                Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
            }
            _ => None,
        }
    }

    /// Resolve a string term to a concrete value, allowing NF-derived constants.
    pub(super) fn resolve_string_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        if let Some(s) = Self::resolve_string_term(terms, state, t, 0) {
            return Some(s);
        }

        let rep = state.find(t);
        self.normal_forms
            .get(&rep)
            .and_then(|nf| self.nf_to_constant(terms, state, nf))
    }

    /// Resolve an integer term to a concrete value with NF-derived string args.
    pub(super) fn resolve_int_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<BigInt> {
        if let Some(n) = Self::resolve_int_term(terms, state, t, 0) {
            return Some(n);
        }
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.indexof" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let pat = self.resolve_string_term_effort1(terms, state, args[1])?;
                let start = self.resolve_int_term_effort1(terms, state, args[2])?;
                crate::eval::eval_str_indexof(&s, &pat, &start)
            }
            "str.len" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(BigInt::from(s.chars().count()))
            }
            "str.to_int" | "str.to.int" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_int(&s))
            }
            "str.to_code" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_code(&s))
            }
            _ => None,
        }
    }

    /// Effort-1 reduction for string-valued extf applications.
    pub(super) fn try_reduce_string_term_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.at" if args.len() == 2 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let i = self.resolve_int_term_effort1(terms, state, args[1])?;
                crate::eval::eval_str_at(&s, &i)
            }
            "str.substr" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let i = self.resolve_int_term_effort1(terms, state, args[1])?;
                let j = self.resolve_int_term_effort1(terms, state, args[2])?;
                crate::eval::eval_str_substr(&s, &i, &j)
            }
            "str.replace" if args.len() == 3 => {
                if state.find(args[0]) == state.find(args[1]) {
                    return self.resolve_string_term_effort1(terms, state, args[2]);
                }
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t_str = self.resolve_string_term_effort1(terms, state, args[1])?;
                let u = self.resolve_string_term_effort1(terms, state, args[2])?;
                Some(crate::eval::eval_str_replace(&s, &t_str, &u))
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = self.resolve_int_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_from_int(&n))
            }
            "str.replace_all" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t_str = self.resolve_string_term_effort1(terms, state, args[1])?;
                let u = self.resolve_string_term_effort1(terms, state, args[2])?;
                Some(crate::eval::eval_str_replace_all(&s, &t_str, &u))
            }
            "str.replace_re" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t = self.resolve_string_term_effort1(terms, state, args[2])?;
                Self::eval_str_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                let t = self.resolve_string_term_effort1(terms, state, args[2])?;
                Self::eval_str_replace_re_all(terms, &s, args[1], &t)
            }
            "str.from_code" if args.len() == 1 => {
                let n = self.resolve_int_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_from_code(&n))
            }
            "str.to_lower" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_lower(&s))
            }
            "str.to_upper" if args.len() == 1 => {
                let s = self.resolve_string_term_effort1(terms, state, args[0])?;
                Some(crate::eval::eval_str_to_upper(&s))
            }
            _ => None,
        }
    }
}
