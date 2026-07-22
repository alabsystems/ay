// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer-valued string function reduction pass.
//!
//! Evaluates str.to_int, str.indexof, str.to_code against asserted integer
//! values and detects conflicts from impossible equalities/inequalities.
//! Extracted from extf_pass.rs as part of #5970 code-health splits.

use super::*;

impl CoreSolver {
    /// Evaluate integer-valued string functions and check for conflicts.
    ///
    /// For each asserted relation involving str.to_int, str.indexof, or
    /// str.to_code, evaluate if possible and compare against asserted
    /// integer values. Also detect impossible inequalities caused purely
    /// by function output ranges (e.g., str.to_int(x) < -2).
    pub(super) fn check_extf_int_reductions(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, relation_expected) = Self::atom_and_polarity(terms, lit);
            let TermData::App(rel_sym, rel_args) = terms.get(atom) else {
                continue;
            };
            if rel_args.len() != 2 {
                continue;
            }

            match rel_sym.name() {
                "=" => {
                    // Try both orientations: f(x) = N and N = f(x).
                    for (func_side, const_side) in
                        [(rel_args[0], rel_args[1]), (rel_args[1], rel_args[0])]
                    {
                        if !Self::is_reducible_int_app(terms, func_side) {
                            continue;
                        }

                        let evaluated = Self::try_reduce_int_term(terms, state, func_side);
                        if let Some(ref reduced) = evaluated {
                            let rhs_value = Self::resolve_int_term(terms, state, const_side, 0);
                            if let Some(ref exp) = rhs_value {
                                let actual = reduced == exp;
                                if actual != relation_expected {
                                    // Soundness guard (regex eval gap): if this
                                    // reduction relies on a str.at/str.substr
                                    // extraction resolving to "" while its base
                                    // string is forced non-empty by a non-nullable
                                    // regex, downgrade to incomplete (Unknown)
                                    // rather than a possibly-wrong UNSAT.
                                    if self.atom_underconstrained_by_regex(terms, state, func_side)
                                    {
                                        if *DEBUG_STRING_CORE {
                                            eprintln!(
                                                "[STRING_CORE] int_reduction: conflict suppressed (regex under-constrained empty) func={func_side:?}"
                                            );
                                        }
                                        self.incomplete = true;
                                        continue;
                                    }
                                    if *DEBUG_STRING_CORE {
                                        // Show detailed resolution info to trace false conflicts.
                                        let func_args_info = if let TermData::App(sym, args) =
                                            terms.get(func_side)
                                        {
                                            let s_str = if !args.is_empty() {
                                                Self::resolve_string_term(terms, state, args[0], 0)
                                            } else {
                                                None
                                            };
                                            format!("{}(s={s_str:?},...)", sym.name())
                                        } else {
                                            "non-app".to_string()
                                        };
                                        let const_info = if let TermData::App(sym, _args) =
                                            terms.get(const_side)
                                        {
                                            let rep = state.find(const_side);
                                            format!("{}(rep={rep:?})", sym.name())
                                        } else {
                                            let crep = state.find(const_side);
                                            format!("const_rep={crep:?}")
                                        };
                                        eprintln!("[STRING_CORE] int_reduction conflict: func={func_args_info} reduced={reduced}, const={const_info} resolved={exp}, expected={relation_expected}, atom={atom:?}");
                                    }
                                    let mut explanation = vec![lit];
                                    Self::add_arg_resolution_explanations(
                                        terms,
                                        state,
                                        func_side,
                                        &mut explanation,
                                    );
                                    // Also explain the const_side's arg resolutions.
                                    // When const_side is str.len(x), resolve_int_term
                                    // resolves x via the string EQC.  If this resolution
                                    // path differs from the EQC constant path (line
                                    // 2900-2903), the explanation must include the string
                                    // EQC merge reasons for x in the const_side, not
                                    // just the func_side.
                                    Self::add_arg_resolution_explanations(
                                        terms,
                                        state,
                                        const_side,
                                        &mut explanation,
                                    );
                                    // The const_side's OWN top-level EQC merge:
                                    // `resolve_int_term` reads the constant off
                                    // `find(const_side)` BEFORE any structural
                                    // descent, and for a BARE Int variable the
                                    // arg-resolution walk above adds nothing.
                                    // Omitting the merge reason (e.g. a branch
                                    // decision `i ≃ 0`) universalizes this
                                    // branch-local conflict — false UNSAT
                                    // (falseunsat_indexof_substr_oob).
                                    Self::add_term_resolution_explanation(
                                        terms,
                                        state,
                                        const_side,
                                        &mut explanation,
                                    );
                                    if *DEBUG_STRING_CORE {
                                        for elit in &explanation {
                                            let tdata = terms.get(elit.term);
                                            eprintln!(
                                                "[STRING_CORE]   expl lit: {:?} val={} term={:?}",
                                                elit.term, elit.value, tdata
                                            );
                                        }
                                    }
                                    infer.add_conflict(
                                        InferenceKind::PredicateConflict,
                                        explanation,
                                    );
                                    return true;
                                }
                            } else if !relation_expected {
                                // For negated equalities, unresolved RHS can hide a
                                // contradiction if it later resolves to the same value.
                                // CAP-2: request an exact reduction lemma when one is
                                // available before latching incomplete.
                                self.note_unreduced_int_app(terms, state, func_side);
                            }
                        } else {
                            // Reducible int app exists but couldn't be reduced (argument
                            // not resolved).
                            if !relation_expected {
                                // Negated equalities always need incomplete: a negated
                                // equality like NOT(str.to_int(x) = 3) might hide a
                                // conflict if x later resolves to "3".
                                // CAP-2: reduction lemma first, incomplete as fallback.
                                self.note_unreduced_int_app(terms, state, func_side);
                            } else if Self::is_range_restricted_int_app(terms, func_side) {
                                // For positive equalities involving range-restricted
                                // functions (str.to_int, str.to_code, str.indexof),
                                // check if the asserted value is outside the valid
                                // range. If so, raise a conflict immediately.
                                // Otherwise, mark incomplete because the LIA solver
                                // treats these as uninterpreted and can't enforce the
                                // range constraint.
                                let rhs_value = Self::resolve_int_term(terms, state, const_side, 0);
                                if let Some(ref val) = rhs_value {
                                    // Only a SYNTACTIC Int literal bound holds in every
                                    // model. A model-resolved (EQC/NF-derived) bound makes
                                    // this conflict model-local, so broadcasting it as a
                                    // universal PredicateConflict is a spurious UNSAT
                                    // (#str-lia-WU). Fail closed (incomplete) otherwise.
                                    if !Self::is_in_valid_range(terms, state, func_side, val)
                                        && matches!(
                                            terms.get(const_side),
                                            TermData::Const(Constant::Int(_))
                                        )
                                    {
                                        let explanation = vec![lit];
                                        infer.add_conflict(
                                            InferenceKind::PredicateConflict,
                                            explanation,
                                        );
                                        return true;
                                    }
                                }
                                // Value is in valid range but can't verify.
                                // CAP-2: request an exact reduction lemma when one is
                                // available (str.indexof); otherwise mark incomplete
                                // so we don't return false SAT.
                                self.note_unreduced_int_app(terms, state, func_side);
                            }
                            // For positive equalities with non-range-restricted
                            // functions (none currently, but future-proofing), do NOT
                            // mark incomplete — the LIA solver handles consistency.
                        }
                    }
                }
                "<" | "<=" => {
                    // Try both orientations:
                    // - f(x) < N / f(x) <= N
                    // - N < f(x) / N <= f(x)  (normalized > / >=)
                    for (func_side, const_side, func_on_left) in [
                        (rel_args[0], rel_args[1], true),
                        (rel_args[1], rel_args[0], false),
                    ] {
                        if !Self::is_reducible_int_app(terms, func_side) {
                            continue;
                        }
                        let Some(relation) = Self::relation_for_int_app(
                            rel_sym.name(),
                            func_on_left,
                            relation_expected,
                        ) else {
                            continue;
                        };

                        let evaluated = Self::try_reduce_int_term(terms, state, func_side);
                        let Some(bound) = Self::resolve_int_term(terms, state, const_side, 0)
                        else {
                            continue;
                        };

                        if let Some(reduced) = evaluated {
                            if !Self::relation_holds(relation, &reduced, &bound) {
                                let mut explanation = vec![lit];
                                Self::add_arg_resolution_explanations(
                                    terms,
                                    state,
                                    func_side,
                                    &mut explanation,
                                );
                                // Also explain the const_side's argument resolutions
                                // (mirrors the `=` branch above). When `const_side` is
                                // e.g. `str.len(str.++ "12" (str.replace s "ab" "7"))`,
                                // the resolved `bound` depends on `s`'s EQC constant
                                // (e.g. `s = ""`). Omitting that dependency makes the
                                // blocking clause forbid the inequality UNIVERSALLY
                                // instead of branch-locally — a wrong UNSAT
                                // (#str-isdigit-fromint, inequality variant).
                                Self::add_arg_resolution_explanations(
                                    terms,
                                    state,
                                    const_side,
                                    &mut explanation,
                                );
                                // The const_side's OWN top-level EQC merge (see
                                // the `=` branch above): a bare Int variable
                                // resolved to a constant by a branch decision
                                // contributes NOTHING to the arg-resolution
                                // walk, so its merge reason must be added here
                                // or the conflict universalizes — false UNSAT.
                                Self::add_term_resolution_explanation(
                                    terms,
                                    state,
                                    const_side,
                                    &mut explanation,
                                );
                                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                                return true;
                            }
                        } else if Self::is_range_restricted_int_app(terms, func_side)
                            && !Self::range_has_witness_for_relation(
                                terms, state, func_side, relation, &bound,
                            )
                        {
                            // Only fire on a SYNTACTIC Int literal bound; a model-
                            // resolved bound (e.g. to_int(str.at ...) collapsing to -1
                            // when n1 is decided out-of-bounds) makes the no-witness
                            // conclusion model-local -> spurious universal UNSAT
                            // (#str-lia-WU). Fail closed otherwise.
                            if matches!(terms.get(const_side), TermData::Const(Constant::Int(_))) {
                                let explanation = vec![lit];
                                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                                return true;
                            }
                            // CAP-2: reduction lemma first, incomplete as fallback.
                            self.note_unreduced_int_app(terms, state, func_side);
                        }
                    }
                }
                _ => {}
            }
        }
        infer.has_conflict()
    }
}
