// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Helper predicates and utility methods for effort-1 extended function evaluation.
//!
//! Equality rewrites, predicate classification, argument explanation,
//! reducibility checks, range validation, and integer function bounds.
//! The main evaluation loop is in `extf_effort1`.

use super::*;

impl CoreSolver {
    /// CVC5 `checkExtfInference` (part 3): apply limited equality rewrites for
    /// non-predicate extf terms equal to constants.
    pub(super) fn check_extf_equality_rewrites_effort1(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) {
        for &lit in state.assertions() {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);
            if !expected {
                continue;
            }
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }

            if let Some((lhs, rhs, mut explanation)) =
                Self::rewrite_extf_equality_effort1(terms, state, args[0], args[1])
            {
                if state.find(lhs) != state.find(rhs) {
                    let mut full_expl = vec![lit];
                    full_expl.append(&mut explanation);
                    Self::add_arg_resolution_explanations(terms, state, args[0], &mut full_expl);
                    infer.add_internal_equality(InferenceKind::Unify, lhs, rhs, full_expl);
                }
            }
            if let Some((lhs, rhs, mut explanation)) =
                Self::rewrite_extf_equality_effort1(terms, state, args[1], args[0])
            {
                if state.find(lhs) != state.find(rhs) {
                    let mut full_expl = vec![lit];
                    full_expl.append(&mut explanation);
                    Self::add_arg_resolution_explanations(terms, state, args[1], &mut full_expl);
                    infer.add_internal_equality(InferenceKind::Unify, lhs, rhs, full_expl);
                }
            }
        }
    }

    /// Rewrite a limited subset of extf equalities `extf_term = const_term`
    /// to a simpler equality if the rewrite is semantics-preserving.
    pub(super) fn rewrite_extf_equality_effort1(
        terms: &TermStore,
        state: &SolverState,
        extf_term: TermId,
        const_term: TermId,
    ) -> Option<(TermId, TermId, Vec<TheoryLit>)> {
        if !matches!(terms.get(const_term), TermData::Const(Constant::String(_))) {
            return None;
        }

        let TermData::App(sym, args) = terms.get(extf_term) else {
            return None;
        };
        match sym.name() {
            // str.replace(s, s, u) == u.
            "str.replace" if args.len() == 3 => {
                if state.find(args[0]) != state.find(args[1]) {
                    return None;
                }
                let mut explanation = Vec::new();
                Self::append_rep_explanation_if_needed(state, args[0], args[1], &mut explanation);
                Some((args[2], const_term, explanation))
            }
            _ => None,
        }
    }

    /// Normalize a theory literal into `(atom, expected_truth_value)`.
    ///
    /// If the asserted literal is a negated atom, fold the negation into the
    /// expected truth value.
    pub(super) fn atom_and_polarity(terms: &TermStore, lit: TheoryLit) -> (TermId, bool) {
        match terms.get(lit.term) {
            TermData::Not(inner) => (*inner, !lit.value),
            _ => (lit.term, lit.value),
        }
    }

    /// Whether `atom` is a supported extf predicate atom.
    pub(super) fn is_extf_predicate_atom(terms: &TermStore, atom: TermId) -> bool {
        let TermData::App(sym, args) = terms.get(atom) else {
            return false;
        };
        match sym.name() {
            "str.contains" | "str.prefixof" | "str.suffixof" | "str.<=" | "str.<" => {
                args.len() == 2
            }
            "str.is_digit" => args.len() == 1,
            _ => false,
        }
    }

    /// Whether an unresolved predicate atom must force `Unknown`.
    ///
    /// Positive `str.contains`, `str.prefixof`, and `str.suffixof` are
    /// satisfiable by witness construction (Skolem decomposition captures
    /// their semantics as concat equations). Only negated forms need to
    /// stay incomplete, as they constrain the model and could hide conflicts.
    pub(super) fn unresolved_predicate_requires_unknown(
        terms: &TermStore,
        atom: TermId,
        expected: bool,
    ) -> bool {
        let TermData::App(sym, _) = terms.get(atom) else {
            return false;
        };
        match sym.name() {
            "str.contains" | "str.prefixof" | "str.suffixof" => !expected,
            _ => true,
        }
    }

    /// Explain why `t` ITSELF resolves to its EQC representative / constant.
    ///
    /// Mirrors the FIRST step of `resolve_int_term`, which reads a constant
    /// off `find(t)` BEFORE any structural descent.
    /// `add_arg_resolution_explanations` only covers the ARGUMENTS of an App
    /// (and no-ops entirely on a bare variable), so a conflict whose
    /// `const_side` is a plain integer variable merged with a constant by a
    /// SAT-branch decision (e.g. `i ≃ 0` while `str.indexof(...)` reduces to
    /// `-1`) omitted the merge reason from the blocking clause —
    /// universalizing a branch-local conflict into a false UNSAT
    /// (falseunsat_indexof_substr_oob witness). Adding the reason only
    /// WEAKENS the learned clause (conditions it on the merge), so this is
    /// always sound.
    pub(super) fn add_term_resolution_explanation(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        explanation: &mut Vec<TheoryLit>,
    ) {
        let rep = state.find(t);
        if rep != t {
            explanation.extend(state.explain(t, rep));
        }
        if let Some(const_id) = state.find_constant_term_id(terms, t) {
            if const_id != t {
                explanation.extend(state.explain(t, const_id));
            }
        }
    }

    /// For an App term, explain why each argument resolves to its EQC
    /// representative. Adds `explain(arg, find(arg))` for each arg where
    /// `find(arg) != arg`.
    pub(super) fn add_arg_resolution_explanations(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        explanation: &mut Vec<TheoryLit>,
    ) {
        let mut visited = HashSet::default();
        Self::add_arg_resolution_explanations_recursive(terms, state, t, explanation, &mut visited);
    }

    /// Recursively explain why each argument of a term resolved to its concrete
    /// value. This mirrors the recursive resolution path in `resolve_string_term`:
    /// when a compound string term like `str.++(a, b)` is resolved by recursively
    /// resolving `a` and `b`, the explanation must include the EQC merge reasons
    /// for each sub-argument — not just the top-level argument.
    ///
    /// Without this recursive walk, conflicts from `check_extf_int_reductions`
    /// produce blocking clauses that are too strong (e.g., blocking
    /// `str.to_int(a++a) = 0` universally when the conflict only holds under
    /// `a = ""`), causing false UNSAT.
    ///
    /// # Why this walk is unconditional and un-capped
    ///
    /// Explanations are asymmetric in their failure modes. Every literal added
    /// here is one that HOLDS in the current assignment, so adding a literal the
    /// resolver did not actually need only makes the blocking clause less
    /// general — sound, merely weaker pruning. OMITTING a literal the resolver
    /// did rely on makes the clause claim something that is not implied, which
    /// forbids the atom unconditionally instead of branch-locally: a wrong
    /// UNSAT. Over-explaining is safe; under-explaining is not.
    ///
    /// This walk therefore descends into EVERY `App` argument rather than a
    /// hand-maintained list of resolver symbols, and carries no depth cap:
    ///
    /// * A symbol whitelist has to mirror the resolver's descent set exactly,
    ///   and silently produces wrong UNSATs the moment it drifts. That drift is
    ///   not hypothetical — it caused #4057 and #str-isdigit-fromint, each
    ///   fixed by appending another name. Descending unconditionally makes the
    ///   class unrepresentable instead of re-fixable.
    /// * A depth cap is a silent truncation, i.e. exactly the unsound
    ///   direction. The resolvers keep their `MAX_RESOLVE_DEPTH` budget because
    ///   they fail CLOSED there (`None` ⇒ unresolved ⇒ no conflict at all);
    ///   an explainer has no such safe direction to fail in.
    ///
    /// Termination and cost come from `visited` instead: the term store is a
    /// hash-consed DAG, so a visited set alone guarantees termination and makes
    /// the walk linear in distinct subterms — strictly better than the previous
    /// code, which could re-traverse a shared subterm once per path to it.
    pub(super) fn add_arg_resolution_explanations_recursive(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        explanation: &mut Vec<TheoryLit>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(t) {
            // Already fully explained via another path; its literals are in.
            return;
        }
        let TermData::App(_, args) = terms.get(t) else {
            return;
        };
        for &arg in args {
            let rep = state.find(arg);
            if rep != arg {
                explanation.extend(state.explain(arg, rep));
            }
            if let Some(const_id) = state.find_constant_term_id(terms, arg) {
                if const_id != arg {
                    explanation.extend(state.explain(arg, const_id));
                }
            }
            // Descend into every compound argument, not just the ones the
            // resolver is currently known to descend through. See the doc
            // comment: matching the resolver's symbol set by hand is what
            // produced #4057 and #str-isdigit-fromint, and an argument the
            // resolver does NOT descend into costs only a few redundant
            // literals here, never soundness.
            if matches!(terms.get(arg), TermData::App(..)) {
                Self::add_arg_resolution_explanations_recursive(
                    terms,
                    state,
                    arg,
                    explanation,
                    visited,
                );
            }
        }
    }

    /// Effort-1 variant: explain why each string argument of an extf atom
    /// resolved to its concrete value. Unlike `add_arg_resolution_explanations`
    /// (which only covers EQC constant paths), this also covers NF resolution.
    ///
    /// When `resolve_string_term_effort1` resolves an arg via its normal form
    /// (not a direct EQC constant), the explanation must include:
    /// 1. The NF deps (how the NF was computed from EQC merges).
    /// 2. Component-to-constant equalities (how each NF base component got
    ///    its constant value).
    ///
    /// Soundness fix for #4057: without NF-level explanations, effort-1
    /// predicate conflicts produce blocking clauses that are too strong,
    /// poisoning the CEGAR search and causing false UNSAT.
    pub(super) fn add_effort1_arg_resolution_explanations(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        explanation: &mut Vec<TheoryLit>,
    ) {
        let TermData::App(_, args) = terms.get(t) else {
            return;
        };
        let mut visited = HashSet::default();
        for &arg in args {
            self.add_effort1_resolution_explanation_recursive(
                terms,
                state,
                arg,
                explanation,
                &mut visited,
            );
        }
    }

    /// Recursively explain why a (sub-)term resolved to a concrete string in the
    /// effort-1 pass. Mirrors the recursive descent of `resolve_string_term` /
    /// `resolve_string_term_effort1`: when a compound term like `str.++(a, b)`
    /// is resolved by recursively resolving each child, the explanation must
    /// include the EQC-merge / NF reasons for EACH child — not just the
    /// top-level argument.
    ///
    /// Soundness fix: a positive `str.contains(str.++("ab", y), "cd")` becomes
    /// branch-locally false once `y` resolves to `""` (so the concat resolves
    /// to `"ab"`). Without explaining `y = ""`, the predicate-conflict blocking
    /// clause is just `¬contains(...)`, which forbids the atom universally and
    /// yields a wrong UNSAT. Recursing here captures the `y = ""` dependency so
    /// the conflict is branch-local (matching the non-effort-1
    /// `add_arg_resolution_explanations_recursive`).
    ///
    /// Unconditional and un-capped for the same reason as
    /// `add_arg_resolution_explanations_recursive` — see that doc comment for
    /// why over-explaining is sound and truncation is not.
    pub(super) fn add_effort1_resolution_explanation_recursive(
        &self,
        terms: &TermStore,
        state: &SolverState,
        arg: TermId,
        explanation: &mut Vec<TheoryLit>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(arg) {
            return;
        }
        // Basic EQC-level explanations (arg -> rep, arg -> constant).
        let rep = state.find(arg);
        if rep != arg {
            explanation.extend(state.explain(arg, rep));
        }
        if let Some(const_id) = state.find_constant_term_id(terms, arg) {
            if const_id != arg {
                explanation.extend(state.explain(arg, const_id));
            }
        }
        // NF-level explanations when the arg was resolved via NF. If the EQC has
        // no direct constant but a NF that resolves to a constant, include the
        // NF deps and component-to-constant proofs.
        if let Some(nf) = self.normal_forms.get(&rep) {
            for dep in &nf.deps {
                explanation.extend(state.explain(dep.lhs, dep.rhs));
            }
            for &component in &nf.base {
                if let Some(comp_const) = state.find_constant_term_id(terms, component) {
                    if component != comp_const {
                        explanation.extend(state.explain(component, comp_const));
                    }
                }
            }
        }
        // Recurse into every compound argument so nested component resolutions
        // (the `y` inside `str.++("ab", y)`, the `s` inside
        // `str.from_int(str.to_int s)`) are explained. This deliberately does
        // NOT try to mirror which symbols `resolve_string_term_effort1` /
        // `resolve_int_term_effort1` descend through: omitting one that they do
        // descend through drops a real dependency and forbids the predicate
        // unconditionally (wrong UNSAT, #str-isdigit-fromint), while including
        // one they do not costs a redundant literal and nothing else.
        if let TermData::App(_, sub_args) = terms.get(arg) {
            let sub_args: Vec<TermId> = sub_args.clone();
            for sub in sub_args {
                self.add_effort1_resolution_explanation_recursive(
                    terms,
                    state,
                    sub,
                    explanation,
                    visited,
                );
            }
        }
    }

    /// Whether `t` is a supported value-returning extf app.
    pub(super) fn is_reducible_string_app(terms: &TermStore, t: TermId) -> bool {
        let TermData::App(sym, args) = terms.get(t) else {
            return false;
        };
        matches!(sym.name(), "str.at" if args.len() == 2)
            || matches!(sym.name(), "str.substr" if args.len() == 3)
            || matches!(sym.name(), "str.replace" | "str.replace_all" | "str.replace_re" | "str.replace_re_all" if args.len() == 3)
            || matches!(sym.name(), "str.from_int" | "int.to.str" | "str.from_code" | "str.to_lower" | "str.to_upper" if args.len() == 1)
    }

    /// Whether `t` is a reducible integer-valued string function application.
    pub(super) fn is_reducible_int_app(terms: &TermStore, t: TermId) -> bool {
        let TermData::App(sym, args) = terms.get(t) else {
            return false;
        };
        matches!(sym.name(), "str.to_int" | "str.to.int" if args.len() == 1)
            || matches!(sym.name(), "str.indexof" if args.len() == 3)
            || matches!(sym.name(), "str.to_code" if args.len() == 1)
    }

    /// Whether `t` is a range-restricted integer-valued string function.
    ///
    /// All functions in `is_reducible_int_app` have restricted ranges under
    /// SMT-LIB 2.6 semantics:
    /// - `str.to_int`: {-1} ∪ ℤ≥0
    /// - `str.indexof`: {-1} ∪ ℤ≥0
    /// - `str.to_code`: {-1} ∪ [0, 196607]
    ///
    /// The LIA solver treats these as uninterpreted and cannot enforce range
    /// constraints. When the function argument is unresolved and a positive
    /// equality asserts a specific value, this classification determines
    /// whether the solver must remain incomplete.
    pub(super) fn is_range_restricted_int_app(terms: &TermStore, t: TermId) -> bool {
        Self::is_reducible_int_app(terms, t)
    }

    /// Whether `val` is in the valid output range of the function `t`.
    ///
    /// Returns `false` if the value is provably outside the function's range,
    /// meaning the equality `t = val` is unsatisfiable regardless of arguments.
    /// When `state` is available, uses length information to narrow str.to_code
    /// range (#6353).
    pub(super) fn is_in_valid_range(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        val: &BigInt,
    ) -> bool {
        let Some((min, max)) = Self::int_app_bounds_with_state(terms, Some(state), t) else {
            return true;
        };
        *val >= min && max.is_none_or(|m| *val <= m)
    }

    pub(super) fn relation_for_int_app(
        op: &str,
        func_on_left: bool,
        expected_truth: bool,
    ) -> Option<IntRelation> {
        match (op, func_on_left, expected_truth) {
            ("<", true, true) => Some(IntRelation::Lt),
            ("<", true, false) => Some(IntRelation::Ge),
            ("<", false, true) => Some(IntRelation::Gt),
            ("<", false, false) => Some(IntRelation::Le),
            ("<=", true, true) => Some(IntRelation::Le),
            ("<=", true, false) => Some(IntRelation::Gt),
            ("<=", false, true) => Some(IntRelation::Ge),
            ("<=", false, false) => Some(IntRelation::Lt),
            _ => None,
        }
    }

    pub(super) fn relation_holds(relation: IntRelation, lhs: &BigInt, rhs: &BigInt) -> bool {
        match relation {
            IntRelation::Lt => lhs < rhs,
            IntRelation::Le => lhs <= rhs,
            IntRelation::Gt => lhs > rhs,
            IntRelation::Ge => lhs >= rhs,
        }
    }

    pub(super) fn range_has_witness_for_relation(
        terms: &TermStore,
        state: &SolverState,
        func_term: TermId,
        relation: IntRelation,
        bound: &BigInt,
    ) -> bool {
        let Some((min, max)) = Self::int_app_bounds_with_state(terms, Some(state), func_term)
        else {
            return true;
        };
        match relation {
            IntRelation::Lt => &min < bound,
            IntRelation::Le => &min <= bound,
            IntRelation::Gt => max.is_none_or(|m| &m > bound),
            IntRelation::Ge => max.is_none_or(|m| &m >= bound),
        }
    }

    /// State-aware integer function bounds.
    ///
    /// When `state` is provided and the function is `str.to_code(x)` with
    /// `len(x) = 1` known, the range narrows from `{-1} ∪ [0, 196607]` to
    /// `[0, 196607]`. The `-1` return value only occurs when `len(x) != 1`,
    /// so the length constraint eliminates it.
    ///
    /// This prevents false SAT on assertions like `(< (str.to_code x) 0)`
    /// when `(= (str.len x) 1)` is asserted (#6353).
    pub(super) fn int_app_bounds_with_state(
        terms: &TermStore,
        state: Option<&SolverState>,
        t: TermId,
    ) -> Option<(BigInt, Option<BigInt>)> {
        let TermData::App(sym, args) = terms.get(t) else {
            return None;
        };
        match sym.name() {
            "str.to_int" | "str.to.int" | "str.indexof" => Some((BigInt::from(-1), None)),
            "str.to_code" if args.len() == 1 => {
                // str.to_code(x) returns -1 when len(x) != 1, and a value
                // in [0, 196607] when len(x) = 1. If len(x) = 1 is known
                // via the solver state, tighten the lower bound to 0.
                let len_is_one = state
                    .is_some_and(|s| s.known_length_full(terms, args[0]).is_some_and(|n| n == 1));
                let min = if len_is_one {
                    BigInt::from(0)
                } else {
                    BigInt::from(-1)
                };
                Some((min, Some(BigInt::from(196_607))))
            }
            "str.to_code" => Some((BigInt::from(-1), Some(BigInt::from(196_607)))),
            _ => None,
        }
    }
}
