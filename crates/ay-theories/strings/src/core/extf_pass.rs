// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function pass: predicate evaluation and string equality checking.
//!
//! Evaluates extf predicates and checks string equalities/disequalities
//! using ground (EQC constant) resolution. Runs before normal-form
//! computation (effort 0).
//!
//! String reductions + helpers: see `extf_pass_reductions.rs`
//! Integer reductions: see `extf_pass_int.rs`

use super::*;

impl CoreSolver {
    /// Evaluate extf Boolean predicates with fully-resolved constant arguments.
    ///
    /// Phase C soundness bridge: if a predicate atom (for example,
    /// `str.contains(x, "abc")`) has arguments that resolve to concrete strings
    /// via EQC constants, evaluate it and detect truth-value contradictions.
    pub(super) fn check_extf_predicates(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, expected) = Self::atom_and_polarity(terms, lit);

            if !Self::is_extf_predicate_atom(terms, atom) {
                continue;
            }
            if self.reduced_terms.contains(&atom) {
                continue;
            }

            let Some(actual) = Self::eval_extf_predicate(terms, state, atom) else {
                // CTN_LEN_INEQ_NSTRICT: for positive str.contains(x, needle)
                // where needle structurally contains x, infer that extra
                // components must be empty. len(needle) >= len(x) always holds,
                // so contains(x, needle) ⇒ x = needle ⇒ extra = "".
                // CVC5 reference: strings_entail.cpp:945 inferEqsFromContains
                if expected {
                    Self::infer_eqs_from_contains(terms, state, atom, lit, infer);
                    // CTN_LHS_EMPTYSTR: str.contains("", x) → x = "".
                    // The empty string only contains the empty string.
                    // CVC5 reference: core_solver.cpp checkCycles + strings_entail.cpp
                    Self::infer_contains_empty_haystack(terms, state, atom, lit, infer);
                }

                // Unsupported symbolic predicate reasoning must not produce SAT
                // in cases where the asserted polarity could hide unsat cores.
                if Self::unresolved_predicate_requires_unknown(terms, atom, expected) {
                    self.incomplete = true;
                }
                continue;
            };

            if actual != expected {
                // Soundness guard: if this conflict relies on a str.at/str.substr
                // extraction resolving to "" while its base string is forced
                // non-empty by a non-nullable regex membership, the empty value
                // is under-constrained (regex length/char constraints are not
                // propagated to the skolem). Downgrade to incomplete (Unknown)
                // rather than trusting a possibly-wrong UNSAT.
                if self.atom_underconstrained_by_regex(terms, state, atom) {
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] check_extf_predicates: conflict suppressed (regex under-constrained empty) atom={atom:?}"
                        );
                    }
                    self.incomplete = true;
                    continue;
                }
                // Soundness guard (#str-pure-WU false theorem): `actual` came from
                // the entailment evaluator, whose EQC-concat shortcut and NF-derived
                // resolution can transiently evaluate a predicate to a value the
                // ground model does not entail. For a NEGATED predicate that
                // transient `true` fires a spurious hard conflict -> wrong UNSAT.
                // Only emit the conflict when the GROUND-ONLY evaluator reproduces
                // the same contradiction; otherwise fail closed (Unknown). Mirrors
                // the #6309 hardening already applied to the effort1/ground path.
                //
                // #ssl-residue C carve-out: a NEGATED `str.contains(x, w)` whose
                // truth is SEGMENT-ENTAILED — the constant needle `w` occurs
                // entirely inside ONE constant component `C` of a concat in
                // `x`'s EQC (`x ≡ a ++ C ++ b` ⟹ contains(x, w) for ALL a, b) —
                // is forced independently of any skolem content, so the ground
                // evaluator's inability to pin `x` cannot hide a counter-model.
                // The entailment is re-derived here from the current EQC state
                // (never trusted from the transient evaluator) and its EQC-merge
                // reasons join the conflict explanation.
                let mut segment_extra: Option<Vec<TheoryLit>> = None;
                match self.eval_extf_predicate_ground(terms, state, atom) {
                    Some(ground) if ground != expected => {}
                    _ => {
                        if actual && !expected {
                            segment_extra = Self::contains_segment_entailment(terms, state, atom);
                        }
                        if segment_extra.is_none() {
                            if *DEBUG_STRING_CORE {
                                eprintln!(
                                    "[STRING_CORE] check_extf_predicates: conflict suppressed (not ground-provable) atom={atom:?} expected={expected} actual={actual}"
                                );
                            }
                            self.incomplete = true;
                            continue;
                        }
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] check_extf_predicates: negated-contains conflict segment-entailed atom={atom:?}"
                            );
                        }
                    }
                }
                // Explanation: the assertion itself + why each argument
                // resolved to its representative constant.
                let mut explanation = vec![lit];
                Self::add_arg_resolution_explanations(terms, state, atom, &mut explanation);
                if let Some(extra) = segment_extra {
                    for l in extra {
                        if !explanation.contains(&l) {
                            explanation.push(l);
                        }
                    }
                }
                if *DEBUG_STRING_CORE {
                    let atom_name = match terms.get(atom) {
                        TermData::App(sym, _) => sym.name(),
                        _ => "<non-app>",
                    };
                    let arg_debug = match terms.get(atom) {
                        TermData::App(_, args) if args.len() >= 2 => format!(
                            "args=({:?}, {:?}) data=({:?}, {:?}) direct=({:?}, {:?})",
                            args[0],
                            args[1],
                            terms.get(args[0]),
                            terms.get(args[1]),
                            Self::resolve_string_term(terms, state, args[0], 0),
                            Self::resolve_string_term(terms, state, args[1], 0)
                        ),
                        TermData::App(_, args) if args.len() == 1 => format!(
                            "arg={:?} direct={:?}",
                            args[0],
                            Self::resolve_string_term(terms, state, args[0], 0)
                        ),
                        _ => String::from("args=<n/a>"),
                    };
                    eprintln!(
                        "[STRING_CORE] check_extf_predicates conflict: lit={:?} atom={:?} ({}) expected={} actual={} {} expl_len={} expl={:?}",
                        lit,
                        atom,
                        atom_name,
                        expected,
                        actual,
                        arg_debug,
                        explanation.len(),
                        explanation
                    );
                    let expl_terms: Vec<String> = explanation
                        .iter()
                        .map(|l| format!("{:?} => {:?}", l, terms.get(l.term)))
                        .collect();
                    eprintln!(
                        "[STRING_CORE] check_extf_predicates conflict expl_terms={expl_terms:?}"
                    );
                }
                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                return true;
            }
        }

        infer.has_conflict()
    }

    /// Detect ground regex-membership violations early in the core pipeline.
    ///
    /// Soundness fix (#8xxx, str.in_re length-bound non-propagation): when a
    /// `str.in_re(s, R)` is asserted true and the string `s` resolves to a
    /// concrete value via its EQC constant (e.g. the SAT solver branched on
    /// `a = ""`), evaluate the membership directly. If the ground value does
    /// NOT match the asserted polarity, raise a conflict whose explanation
    /// includes the membership literal itself.
    ///
    /// This mirrors `RegExpSolver::check`, but runs as an early core step so
    /// the conflict (which carries `str.in_re` in its explanation) is learned
    /// BEFORE the downstream extf int-reduction / predicate passes raise a
    /// conflict that omits the membership literal. Without this, a model with
    /// `a = ""` was refuted by `str.to_int(str.at(a,0)) = -1` alone, whose
    /// blocking clause `NOT(to_int=...) OR NOT(a="")` does not force `a != ""`.
    /// The membership-derived clause `NOT(in_re) OR NOT(a="")` DOES force the
    /// SAT solver to abandon `a = ""` (since `in_re` is asserted true), so the
    /// non-nullable regex `(re.+ ...)` correctly excludes the empty assignment.
    ///
    /// Only ground (EQC-constant) memberships are evaluated here; non-ground
    /// memberships remain for the regex solver / DPLL splits. This is strictly
    /// a soundness-preserving conflict: it fires only when the current model's
    /// concrete `s` value provably violates the asserted membership.
    pub(super) fn check_regex_membership_violations(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, polarity) = Self::atom_and_polarity(terms, lit);
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }
            let string_term = args[0];
            let regex_term = args[1];

            // Resolve the string to a ground value via its EQC constant.
            let rep = state.find(string_term);
            let Some(s) = state
                .get_eqc(&rep)
                .and_then(|e| e.constant.as_deref())
                .map(ToOwned::to_owned)
                .or_else(|| match terms.get(string_term) {
                    TermData::Const(Constant::String(s)) => Some(s.clone()),
                    _ => None,
                })
            else {
                continue;
            };

            // Evaluate the (possibly non-ground) regex against the concrete
            // string. `None` => regex not ground-evaluable; leave for splits.
            let Some(matches) = RegExpSolver::evaluate(terms, &s, regex_term) else {
                continue;
            };

            if matches != polarity {
                // Ground membership violation. Explanation: the membership
                // literal plus why `string_term` equals its constant rep.
                let mut explanation = vec![lit];
                if let Some(const_id) = state.find_constant_term_id(terms, string_term) {
                    if const_id != string_term {
                        explanation.extend(state.explain(string_term, const_id));
                    }
                }
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] regex membership violation: in_re({string_term:?}={s:?}, {regex_term:?}) eval={matches} polarity={polarity} expl_len={}",
                        explanation.len()
                    );
                }
                infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                return true;
            }
        }
        infer.has_conflict()
    }

    /// Refute `str.in_re(x, R)` when R's accepted-length set is FINITE and the
    /// forced length of `x` is not in it (regex length-set disjointness).
    ///
    /// Completeness improvement (strings_completeness, X2): a regex such as
    /// `(re.union (str.to_re "ab") (str.to_re "cd"))` accepts ONLY strings of
    /// length 2. If the formula also asserts `str.len(x) = 3`, no value of `x`
    /// can satisfy both, so the conjunction is UNSAT. Without this, the SAT
    /// layer enumerates every length-3 candidate string (`"aaa"`, `"aab"`, …)
    /// and refutes each by ground membership evaluation — an exponential blowup
    /// that usually times out to `unknown`.
    ///
    /// SOUNDNESS: `RegExpSolver::accepted_lengths(R)` returns `Some(L)` ONLY for
    /// regexes whose language is finite-length, and then `L` is the EXACT set of
    /// lengths any accepted string can have. So `str.in_re(x, R)` true implies
    /// `len(x) ∈ L`. We fire a conflict only when `len(x)` is a KNOWN concrete
    /// value `n` (from an EQC string constant or an N-O length bridge) AND
    /// `n ∉ L`. The conflict explanation is the membership literal plus the
    /// asserted length-equality literal that fixes `len(x) = n`. If we cannot
    /// recover a sound length reason, we DO NOT fire (fail closed). This never
    /// produces SAT and only emits UNSAT when the two assertions are genuinely
    /// jointly inconsistent.
    pub(super) fn check_regex_length_disjoint(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, polarity) = Self::atom_and_polarity(terms, lit);
            // Only asserted-TRUE memberships impose a length requirement.
            if !polarity {
                continue;
            }
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }
            let string_term = args[0];
            let regex_term = args[1];

            // Exact finite accepted-length set, or `None` (unbounded / unknown).
            let Some(len_set) = RegExpSolver::accepted_lengths(terms, regex_term) else {
                continue;
            };

            // An EMPTY accepted-length set means `R` denotes the EMPTY language:
            // no string of any length is accepted (e.g. `(re.range "ab" "cd")`,
            // `(re.range "z" "a")`, `re.none`, or a length-disjoint `re.inter`).
            // The soundness contract of `accepted_lengths` is "membership implies
            // len(x) ∈ L", so `L = ∅` makes any positive membership
            // unconditionally unsatisfiable, independent of len(x). The
            // membership literal alone is a sound conflict reason — no known
            // length is required.
            if len_set.is_empty() {
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] regex empty-language membership: in_re({string_term:?}, {regex_term:?}) accepts nothing → conflict"
                    );
                }
                infer.add_conflict(InferenceKind::PredicateConflict, vec![lit]);
                return true;
            }

            // The known concrete length of `x`, if any.
            let Some(n) = state.known_length_full(terms, string_term) else {
                continue;
            };

            if len_set.contains(&n) {
                continue;
            }

            // Length-set disjointness: len(x) = n ∉ L(R). Build a sound
            // explanation. Start with the membership literal; add the
            // length-establishing literal(s).
            let mut explanation = vec![lit];
            if !Self::add_length_reason(terms, state, string_term, n, &mut explanation) {
                // No sound length reason recoverable: fail closed, do not fire.
                continue;
            }

            if *DEBUG_STRING_CORE {
                eprintln!(
                    "[STRING_CORE] regex length-set disjoint: in_re({string_term:?}, {regex_term:?}) accepts {len_set:?} but len={n} → conflict expl_len={}",
                    explanation.len()
                );
            }
            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
            return true;
        }
        infer.has_conflict()
    }

    /// Append the literal(s) that establish `len(string_term) = n` to
    /// `explanation`. Returns `true` if a SOUND reason was found and added.
    ///
    /// Two sources are accepted, in priority order:
    /// 1. An asserted-true equality `(= (str.len y) n)` (or commuted) where `y`
    ///    is in the same EQC as `string_term`: the reason is that equality
    ///    literal plus the `string_term ~ y` proof path. PREFERRED because the
    ///    resulting learned clause `¬in_re(x,R) ∨ ¬(len(x)=n)` is a STRONG
    ///    general conflict — the SAT solver cannot escape it by trying a
    ///    different concrete value for `x`.
    /// 2. `string_term` resolves to an EQC string constant of length `n`: the
    ///    reason is the proof-forest path from `string_term` to that constant.
    ///    Weaker (only refutes that one value branch) but still sound.
    ///
    /// Returns `false` (no fire) when neither yields a non-empty sound reason —
    /// e.g. when the length is only known via an N-O bridge whose provenance we
    /// cannot reconstruct here. Failing closed keeps the refutation sound.
    fn add_length_reason(
        terms: &TermStore,
        state: &SolverState,
        string_term: TermId,
        n: usize,
        explanation: &mut Vec<TheoryLit>,
    ) -> bool {
        // Source 1 (preferred): a direct asserted length equality on x's EQC.
        let x_rep = state.find(string_term);
        for &lit in state.assertions() {
            let (lit_atom, lit_pol) = Self::atom_and_polarity(terms, lit);
            if !lit_pol {
                continue;
            }
            let TermData::App(eq_sym, eq_args) = terms.get(lit_atom) else {
                continue;
            };
            if eq_sym.name() != "=" || eq_args.len() != 2 {
                continue;
            }
            // Identify the (str.len y, int n) shape in either order.
            let (a0, a1) = (eq_args[0], eq_args[1]);
            for &(ls, is) in &[(a0, a1), (a1, a0)] {
                let Some(y) = state.get_str_len_arg(terms, ls) else {
                    continue;
                };
                // The int side must be exactly the constant n.
                let matches_n = match terms.get(is) {
                    TermData::Const(Constant::Int(v)) => {
                        v.try_into().map(|vv: usize| vv == n).unwrap_or(false)
                    }
                    _ => state
                        .resolve_int_constant(terms, is)
                        .is_some_and(|v| v >= 0 && (v as usize) == n),
                };
                if !matches_n {
                    continue;
                }
                // y must be the membership subject (same EQC).
                if state.find(y) != x_rep {
                    continue;
                }
                // Sound: this asserted equality fixes len(y)=n and y ~ x.
                let before = explanation.len();
                explanation.push(lit);
                if y != string_term {
                    let path = state.explain(string_term, y);
                    if path.is_empty() {
                        // No proof path: roll back, try other candidates.
                        explanation.truncate(before);
                        continue;
                    }
                    explanation.extend(path);
                }
                return true;
            }
        }

        // Source 2 (fallback): x is in an EQC with a string constant of len n.
        if let Some(const_id) = state.find_constant_term_id(terms, string_term) {
            if let TermData::Const(Constant::String(s)) = terms.get(const_id) {
                if s.chars().count() == n {
                    if const_id != string_term {
                        let path = state.explain(string_term, const_id);
                        if path.is_empty() {
                            return false;
                        }
                        explanation.extend(path);
                    }
                    // If string_term IS the constant, its length is fixed
                    // syntactically; the membership literal already names the
                    // subject. Accept (the conflict is sound by construction).
                    return true;
                }
            }
        }

        false
    }

    /// Whether `t` (a string-sorted term) is a `str.at`/`str.substr` extraction
    /// over a base string that is constrained by a non-nullable regex.
    ///
    /// Soundness guard for the str.at/str.to_int regex eval gap: the eager
    /// DPLL `str.at` / `str.substr` reductions introduce a fresh skolem for the
    /// extracted character/substring, but they do NOT propagate the regex's
    /// per-position character class (nor the implied length lower bound) onto
    /// that skolem. When the base variable `s` carries an asserted-true
    /// `str.in_re(s, R)` with non-nullable `R` (e.g. `(re.+ (re.range "0" "1"))`,
    /// which forces every position of `s` to be a digit), the SAT solver is
    /// free to assign the skolem a value the regex would actually forbid
    /// (including the empty string for an out-of-bounds-by-missing-length
    /// index, or a non-digit character). Conflicts derived from such an
    /// under-constrained extraction value are therefore NOT sound global
    /// refutations. Returning true downgrades the conflict to incomplete
    /// (sound Unknown) instead of a potentially-wrong UNSAT.
    ///
    /// This only ever weakens a conflict to Unknown — it never asserts SAT —
    /// so it cannot introduce unsoundness.
    fn extf_value_underconstrained_by_regex(
        &self,
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        depth: usize,
    ) -> bool {
        if depth > Self::MAX_RESOLVE_DEPTH {
            return false;
        }
        let TermData::App(sym, args) = terms.get(t) else {
            return false;
        };
        match sym.name() {
            "str.at" | "str.substr" if !args.is_empty() => {
                if self.base_constrained_nonnullable_regex(terms, state, args[0]) {
                    return true;
                }
                // Recurse into the base (handles nested str.at(str.substr(...))).
                self.extf_value_underconstrained_by_regex(terms, state, args[0], depth + 1)
            }
            // Compound string terms: recurse into string-valued arguments.
            "str.++" | "str.replace" | "str.replace_all" | "str.replace_re"
            | "str.replace_re_all" | "str.to_lower" | "str.to_upper" => args.iter().any(|&a| {
                matches!(terms.sort(a), Sort::String)
                    && self.extf_value_underconstrained_by_regex(terms, state, a, depth + 1)
            }),
            _ => false,
        }
    }

    /// Whether the string `s` is the subject of an asserted-true `str.in_re`
    /// membership whose regex cannot match the empty string (non-nullable).
    fn base_constrained_nonnullable_regex(
        &self,
        terms: &TermStore,
        state: &SolverState,
        s: TermId,
    ) -> bool {
        let s_rep = state.find(s);
        for &lit in state.assertions() {
            let (atom, polarity) = Self::atom_and_polarity(terms, lit);
            if !polarity {
                continue;
            }
            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }
            if state.find(args[0]) != s_rep {
                continue;
            }
            // Non-nullable regex (cannot accept "") implies a positive length
            // bound that the eager reductions do not propagate.
            if RegExpSolver::is_nullable(terms, args[1]) == Some(false) {
                return true;
            }
        }
        false
    }

    /// Whether any string argument of `atom` is an extf extraction whose empty
    /// value is under-constrained by a non-nullable regex on its base string.
    /// Used to downgrade extf conflicts to Unknown (fail-closed) rather than
    /// returning a potentially-wrong UNSAT.
    pub(super) fn atom_underconstrained_by_regex(
        &self,
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> bool {
        let TermData::App(_, args) = terms.get(atom) else {
            return false;
        };
        args.iter().any(|&a| {
            matches!(terms.sort(a), Sort::String)
                && self.extf_value_underconstrained_by_regex(terms, state, a, 0)
        })
    }

    /// Evaluate asserted string equalities/disequalities involving extf apps.
    ///
    /// Unlike the EQC-constant scan above, this examines all asserted equality
    /// literals, including negated equalities where the extf app and constant are
    /// intentionally in different EQCs.
    pub(super) fn check_extf_string_equalities(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, equality_expected) = Self::atom_and_polarity(terms, lit);
            let TermData::App(eq_sym, eq_args) = terms.get(atom) else {
                continue;
            };
            if eq_sym.name() != "=" || eq_args.len() != 2 {
                continue;
            }

            let lhs = eq_args[0];
            let rhs = eq_args[1];
            if *terms.sort(lhs) != Sort::String || *terms.sort(rhs) != Sort::String {
                continue;
            }

            let lhs_extf = Self::is_reducible_string_app(terms, lhs);
            let rhs_extf = Self::is_reducible_string_app(terms, rhs);
            if !lhs_extf && !rhs_extf {
                continue;
            }
            if (lhs_extf && self.reduced_terms.contains(&lhs))
                || (rhs_extf && self.reduced_terms.contains(&rhs))
            {
                continue;
            }

            let lhs_value = Self::resolve_string_term(terms, state, lhs, 0);
            let rhs_value = Self::resolve_string_term(terms, state, rhs, 0);

            match (lhs_value.as_ref(), rhs_value.as_ref()) {
                (Some(lhs_eval), Some(rhs_eval)) => {
                    let actual = lhs_eval == rhs_eval;
                    if actual != equality_expected {
                        // The triggering assertion + argument resolution reasons.
                        let mut explanation = vec![lit];
                        // Explain why each extf argument resolves to its constant.
                        Self::add_arg_resolution_explanations(terms, state, lhs, &mut explanation);
                        Self::add_arg_resolution_explanations(terms, state, rhs, &mut explanation);
                        infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                        return true;
                    }
                }
                _ => {
                    if !equality_expected
                        && ((lhs_extf && lhs_value.is_none()) || (rhs_extf && rhs_value.is_none()))
                    {
                        self.incomplete = true;
                    }
                }
            }
        }

        infer.has_conflict()
    }
}
