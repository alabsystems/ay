// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Contains/prefix/suffix decomposition pre-registration for string theory.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::super::strings_eval::multi_contains_min_len;

impl Executor {
    /// Collect variables that appear as the first argument of str.at in the
    /// assertion tree. Used by prefix decomposition to emit targeted character
    /// constraints only when str.at interaction is possible (#4118).
    pub(in crate::executor) fn collect_str_at_variables(
        &self,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        let mut result = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "str.at" && args.len() == 2 => {
                    result.insert(args[0]);
                    // Also recurse into args in case they contain nested terms.
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => {
                    stack.push(*inner);
                }
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, val) in bindings {
                        stack.push(*val);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    stack.push(*body);
                }
                _ => {}
            }
        }
        result
    }

    /// Pre-register eager decompositions for positively-asserted `str.contains`.
    ///
    /// For each `str.contains(x, y)` that appears positively in the assertion
    /// tree, emits the CVC5-style eager reduction:
    ///   `str.contains(x, y) => x = str.++(sk_pre, y, sk_post)`
    ///   `len(sk_pre) >= 0`
    ///   `len(sk_post) >= 0`
    ///
    /// The implication ensures the decomposition is only active when the contains
    /// predicate is true. Skolems are created in the executor's TermStore and
    /// persist across CEGAR iterations (unlike CoreSolver state which is reset).
    ///
    /// Reference: CVC5 `extf_solver.cpp:181-202` (checkExtfReductions, effort 1)
    pub(in crate::executor) fn preregister_contains_decompositions(
        &mut self,
        assertions: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
        decomposed_vars: &mut HashSet<TermId>,
        contains_decomposed_vars: &mut HashSet<TermId>,
    ) -> Vec<TermId> {
        let mut decompositions = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();

        // Pre-pass: build index mapping terms to their syntactic concat components.
        // Used to skip decompositions where the needle is already a component.
        let concat_components = self.build_concat_component_index(assertions);
        // Track terms that are syntactically fixed to one string constant by
        // top-level equalities. For these ground haystacks, eager decomposition
        // can over-constrain multiple positive contains atoms (#3919).
        let ground_string_terms = self.collect_top_level_ground_string_terms(assertions);

        // Track variables that already received eager contains decompositions.
        // Used by prefix/suffix handlers to block 2-component decompositions
        // on variables that already have 3-component contains decompositions
        // (#3919, #4055).
        //
        // Multiple *contains* decompositions on the same variable are allowed
        // (#4018): each gets unique skolems keyed on (haystack, needle), and
        // the equality solver reconciles them. This matches CVC5's approach.
        //
        // Prefix and suffix decompositions are compatible with each other:
        // they decompose from opposite ends (x = prefix ++ sk_suffix vs
        // x = sk_prefix ++ suffix). But prefix/suffix (2-component) conflicts
        // with contains (3-component).
        let mut contains_decomposed: HashSet<TermId> = HashSet::default();
        // Track variables with prefix/suffix decompositions so that contains
        // decompositions are blocked for those variables (bidirectional guard).
        // Contains produces a 3-component concat (sk_pre ++ y ++ sk_post) that
        // conflicts with prefix 2-component (s ++ sk) or suffix 2-component
        // (sk ++ s). Multiple prefix/suffix on the same variable is safe (#4118);
        // prefix+contains or suffix+contains is not.
        let mut prefix_suffix_decomposed: HashSet<TermId> = HashSet::default();

        // Collect positive contains atoms with constant needles, grouped by haystack.
        // Used to emit pairwise combined length lower bounds (#3982).
        let mut const_contains_by_var: HashMap<TermId, Vec<(TermId, String)>> = HashMap::default();

        // Pre-pass: collect variables that have str.at terms in the formula.
        // Used to emit targeted character constraints for prefix decompositions
        // (#4118) only when str.at interaction is possible.
        let str_at_vars = self.collect_str_at_variables(assertions);

        // Walk assertions tracking polarity to find positive str.contains atoms.
        // Stack entries: (term, positive_polarity).
        // positive_polarity=true means the term appears in a context where it being
        // true contributes to satisfying the formula.
        let mut stack: Vec<(TermId, bool)> = assertions.iter().map(|&t| (t, true)).collect();
        let mut visited: HashSet<(TermId, bool)> = HashSet::default();

        while let Some((term, positive)) = stack.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args)
                    if name == "str.contains"
                        && args.len() == 2
                        && positive
                        && seen.insert(term) =>
                {
                    let x = args[0];
                    let y = args[1];

                    // Reflexive: str.contains(x, x) is trivially true.
                    // Skip decomposition to avoid cyclic equation
                    // x = str.++(sk, x, sk) which causes false UNSAT.
                    // CVC5 reference: CTN_EQ rewrite, sequences_rewriter.cpp:2815
                    if x == y {
                        continue;
                    }

                    // Eager axiom for empty-string haystack (#3850, rw_15):
                    // str.contains("", x) ⟺ x = "". The empty string
                    // contains only the empty string.
                    if matches!(
                        self.ctx.terms.get(x),
                        TermData::Const(Constant::String(s)) if s.is_empty()
                    ) {
                        let empty = self.ctx.terms.mk_string(String::new());
                        let y_eq_empty = self.ctx.terms.mk_eq(y, empty);
                        // contains("", x) => x = ""
                        decompositions.push(self.ctx.terms.mk_implies(term, y_eq_empty));
                        // x = "" => contains("", x)
                        decompositions.push(self.ctx.terms.mk_implies(y_eq_empty, term));
                        continue;
                    }

                    // Skip eager decomposition when the haystack is already
                    // fixed to a concrete string via top-level equalities.
                    // Direct contains evaluation on the ground value is
                    // sufficient and avoids conflicting skolem encodings.
                    if self.term_has_ground_string_value(&ground_string_terms, x) {
                        continue;
                    }

                    // Record constant-pattern contains for combined length
                    // bounds (#3982). Pairs of constant patterns on the same
                    // variable yield a tighter lower bound than individual ones.
                    // This must happen before decomposition filtering so
                    // length bounds are emitted even if decomposition is skipped.
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(y) {
                        const_contains_by_var
                            .entry(x)
                            .or_default()
                            .push((term, s.clone()));
                    }

                    // Skip decomposition when the needle is already a
                    // syntactic component of the haystack's concat.
                    // E.g., str.contains(y, "world") where y = str.++(x, "world").
                    // Decomposing introduces redundant skolems that cause
                    // the CEGAR loop to stall on NF unification.
                    if Self::needle_in_concat_components(&concat_components, &self.ctx.terms, x, y)
                    {
                        continue;
                    }

                    // Skip when this variable already has a prefix/suffix
                    // decomposition. Contains produces a 3-component
                    // concat (sk_pre ++ y ++ sk_post) that conflicts with
                    // prefix 2-component (s ++ sk) or suffix (sk ++ s).
                    //
                    // Multiple contains decompositions on the same variable
                    // are allowed (#4018): each gets unique skolems keyed
                    // on (haystack, needle), and the equality solver
                    // reconciles them. This matches CVC5's approach
                    // (extf_solver.cpp — d_reduced is per-term, not
                    // per-variable).
                    if prefix_suffix_decomposed.contains(&x) {
                        continue;
                    }
                    contains_decomposed.insert(x);
                    decomposed_vars.insert(x);
                    contains_decomposed_vars.insert(x);

                    // Create skolems for prefix and suffix.
                    let sk_pre = skolem_cache.contains_pre(&mut self.ctx.terms, x, y);
                    let sk_post = skolem_cache.contains_post(&mut self.ctx.terms, x, y);

                    // Build: str.++(sk_pre, y, sk_post)
                    let concat = self.ctx.terms.mk_app(
                        Symbol::named("str.++"),
                        vec![sk_pre, y, sk_post],
                        Sort::String,
                    );
                    // Build: x = str.++(sk_pre, y, sk_post)
                    let eq = self.ctx.terms.mk_eq(x, concat);
                    // Build: str.contains(x, y) => x = str.++(sk_pre, y, sk_post)
                    let implies = self.ctx.terms.mk_implies(term, eq);
                    decompositions.push(implies);

                    // Non-negativity for skolem lengths.
                    let zero_a = self.ctx.terms.mk_int(BigInt::from(0));
                    let len_pre =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![sk_pre], Sort::Int);
                    decompositions.push(self.ctx.terms.mk_ge(len_pre, zero_a));

                    let zero_b = self.ctx.terms.mk_int(BigInt::from(0));
                    let len_post =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![sk_post], Sort::Int);
                    decompositions.push(self.ctx.terms.mk_ge(len_post, zero_b));

                    // Length normalization axiom (CVC5 STRINGS_LEN_NORM):
                    // contains(x, y) => len(x) = len(sk_pre) + len(y) + len(sk_post)
                    // Without this, arithmetic cannot derive len(sk_pre) = 0
                    // from len(x) = 3 and len(y) = 3.
                    // Reference: CVC5 core_solver.cpp:2641-2690
                    let len_x = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
                    let len_y = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);

                    // Constant fold len(y) when y is a string literal.
                    // The main collect_str_len_axioms pass ran before
                    // preregister_contains_decompositions, so these new
                    // str.len applications are not yet constrained.
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(y) {
                        let char_count = s.chars().count();
                        let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
                        decompositions.push(self.ctx.terms.mk_eq(len_y, len_val));
                    }

                    let sum = self.ctx.terms.mk_add(vec![len_pre, len_y, len_post]);
                    let len_eq = self.ctx.terms.mk_eq(len_x, sum);
                    let len_implies = self.ctx.terms.mk_implies(term, len_eq);
                    decompositions.push(len_implies);

                    // lengthPositive bridge for skolems (CVC5 term_registry.cpp:173-185):
                    // len(sk) = 0 => sk = "" and sk = "" => len(sk) = 0
                    // Without this, arithmetic can derive len(sk)=0 but the SAT
                    // solver cannot force sk="".
                    for &sk in &[sk_pre, sk_post] {
                        let len_sk =
                            self.ctx
                                .terms
                                .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                        let zero = self.ctx.terms.mk_int(BigInt::from(0));
                        let len_eq_zero = self.ctx.terms.mk_eq(len_sk, zero);
                        let empty = self.ctx.terms.mk_string(String::new());
                        let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty);
                        // len(sk) = 0 => sk = ""
                        decompositions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                        // sk = "" => len(sk) = 0
                        decompositions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
                    }
                }
                // Don't recurse into str.contains arguments for polarity tracking.
                TermData::App(Symbol::Named(name), args)
                    if name == "str.prefixof"
                        && args.len() == 2
                        && positive
                        && seen.insert(term) =>
                {
                    let s = args[0]; // the prefix pattern
                    let x = args[1]; // the string that has the prefix

                    // Skip if a contains already claimed this variable
                    // (3-component NF conflicts with prefix 2-component).
                    // No per-variable dedup: each prefixof atom gets its
                    // own skolem (#4118 -- old code skipped 2nd prefix).
                    if contains_decomposed.contains(&x) {
                        continue;
                    }
                    // Mark this variable as having a prefix/suffix
                    // decomposition so subsequent contains atoms are
                    // blocked (bidirectional guard).
                    prefix_suffix_decomposed.insert(x);

                    // Create skolem for the remaining suffix.
                    let sk_suffix = skolem_cache.prefix_remainder(&mut self.ctx.terms, x, s);

                    // Build: str.++(s, sk_suffix)
                    let concat = self.ctx.terms.mk_app(
                        Symbol::named("str.++"),
                        vec![s, sk_suffix],
                        Sort::String,
                    );
                    // Build: x = str.++(s, sk_suffix)
                    let eq = self.ctx.terms.mk_eq(x, concat);
                    // Build: str.prefixof(s, x) => x = str.++(s, sk_suffix)
                    let implies = self.ctx.terms.mk_implies(term, eq);
                    decompositions.push(implies);

                    // Non-negativity for skolem length.
                    let zero = self.ctx.terms.mk_int(BigInt::from(0));
                    let len_sk =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![sk_suffix], Sort::Int);
                    decompositions.push(self.ctx.terms.mk_ge(len_sk, zero));

                    // Length normalization:
                    // prefixof(s, x) => len(x) = len(s) + len(sk_suffix)
                    let len_x = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
                    let len_s = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

                    // Constant fold len(s) when s is a string literal.
                    if let TermData::Const(Constant::String(sv)) = self.ctx.terms.get(s) {
                        let char_count = sv.chars().count();
                        let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
                        decompositions.push(self.ctx.terms.mk_eq(len_s, len_val));
                    }

                    let sum = self.ctx.terms.mk_add(vec![len_s, len_sk]);
                    let len_eq = self.ctx.terms.mk_eq(len_x, sum);
                    let len_implies = self.ctx.terms.mk_implies(term, len_eq);
                    decompositions.push(len_implies);

                    // lengthPositive bridge for skolem.
                    {
                        let len_sk2 = self.ctx.terms.mk_app(
                            Symbol::named("str.len"),
                            vec![sk_suffix],
                            Sort::Int,
                        );
                        let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
                        let len_eq_zero = self.ctx.terms.mk_eq(len_sk2, zero2);
                        let empty = self.ctx.terms.mk_string(String::new());
                        let sk_eq_empty = self.ctx.terms.mk_eq(sk_suffix, empty);
                        decompositions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                        decompositions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
                    }

                    // Targeted character constraints (#4118): when the
                    // formula already contains str.at(x, _) terms, emit
                    // prefixof(s, x) => str.at(x, i) = s[i] for each
                    // character position. This connects the prefix to
                    // existing character-level reasoning without creating
                    // unnecessary extf reduction terms.
                    if str_at_vars.contains(&x) {
                        if let TermData::Const(Constant::String(sv)) = self.ctx.terms.get(s) {
                            let sv = sv.clone();
                            for (i, ch) in sv.chars().enumerate() {
                                let idx = self.ctx.terms.mk_int(BigInt::from(i));
                                let at_term = self.ctx.terms.mk_app(
                                    Symbol::named("str.at"),
                                    vec![x, idx],
                                    Sort::String,
                                );
                                let ch_str = self.ctx.terms.mk_string(ch.to_string());
                                let ch_eq = self.ctx.terms.mk_eq(at_term, ch_str);
                                let ch_implies = self.ctx.terms.mk_implies(term, ch_eq);
                                decompositions.push(ch_implies);
                            }
                        }
                    }
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "str.suffixof"
                        && args.len() == 2
                        && positive
                        && seen.insert(term) =>
                {
                    let s = args[0]; // the suffix pattern
                    let x = args[1]; // the string that has the suffix

                    // Skip if a contains already claimed this variable
                    // (3-component NF conflicts with suffix 2-component).
                    // No per-variable dedup: each suffixof atom gets its
                    // own skolem (#4118 -- old code skipped 2nd suffix).
                    // Prefix+suffix coexistence is safe (#4055).
                    if contains_decomposed.contains(&x) {
                        continue;
                    }
                    // Mark this variable as having a prefix/suffix
                    // decomposition so subsequent contains atoms are
                    // blocked (bidirectional guard).
                    prefix_suffix_decomposed.insert(x);

                    // Create skolem for the remaining prefix.
                    let sk_prefix = skolem_cache.suffix_remainder(&mut self.ctx.terms, x, s);

                    // Build: str.++(sk_prefix, s)
                    let concat = self.ctx.terms.mk_app(
                        Symbol::named("str.++"),
                        vec![sk_prefix, s],
                        Sort::String,
                    );
                    // Build: x = str.++(sk_prefix, s)
                    let eq = self.ctx.terms.mk_eq(x, concat);
                    // Build: str.suffixof(s, x) => x = str.++(sk_prefix, s)
                    let implies = self.ctx.terms.mk_implies(term, eq);
                    decompositions.push(implies);

                    // Non-negativity for skolem length.
                    let zero = self.ctx.terms.mk_int(BigInt::from(0));
                    let len_sk =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![sk_prefix], Sort::Int);
                    decompositions.push(self.ctx.terms.mk_ge(len_sk, zero));

                    // Length normalization:
                    // suffixof(s, x) => len(x) = len(sk_prefix) + len(s)
                    let len_x = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
                    let len_s = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

                    // Constant fold len(s) when s is a string literal.
                    if let TermData::Const(Constant::String(sv)) = self.ctx.terms.get(s) {
                        let char_count = sv.chars().count();
                        let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
                        decompositions.push(self.ctx.terms.mk_eq(len_s, len_val));
                    }

                    let sum = self.ctx.terms.mk_add(vec![len_sk, len_s]);
                    let len_eq = self.ctx.terms.mk_eq(len_x, sum);
                    let len_implies = self.ctx.terms.mk_implies(term, len_eq);
                    decompositions.push(len_implies);

                    // lengthPositive bridge for skolem.
                    {
                        let len_sk2 = self.ctx.terms.mk_app(
                            Symbol::named("str.len"),
                            vec![sk_prefix],
                            Sort::Int,
                        );
                        let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
                        let len_eq_zero = self.ctx.terms.mk_eq(len_sk2, zero2);
                        let empty = self.ctx.terms.mk_string(String::new());
                        let sk_eq_empty = self.ctx.terms.mk_eq(sk_prefix, empty);
                        decompositions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                        decompositions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
                    }

                    // Character-level constraints (#4118): for constant
                    // suffix patterns, assert str.at(x, len(x)-len(s)+i) =
                    // char_i. This needs len(x) to be resolved first, so
                    // we only emit constraints when both s and len(x) are
                    // ground (otherwise the str.at index is non-constant).
                    // For suffix, the character position depends on len(x)
                    // which is typically non-ground, so we skip this for
                    // now — suffix character constraints require a different
                    // mechanism (the overlap equalities handle the ground
                    // case).
                }
                TermData::Not(inner) => {
                    stack.push((*inner, !positive));
                }
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    // Conjunction: children inherit parent polarity.
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push((arg, positive));
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "or" => {
                    // Disjunction: children inherit parent polarity.
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push((arg, positive));
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                    // Implication: antecedent has flipped polarity, consequent inherits.
                    let ant = args[0];
                    let con = args[1];
                    stack.push((ant, !positive));
                    stack.push((con, positive));
                }
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    // Equality/iff: children appear in both positive and negative
                    // context. For (not (= P Q)), P can be true-and-Q-false or
                    // P-false-and-Q-true. Without both polarities, positive
                    // str.contains inside negated equivalences never gets its
                    // decomposition registered (#3850).
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push((arg, true));
                        stack.push((arg, false));
                    }
                }
                TermData::App(_, args) => {
                    // Other apps: recurse but don't track polarity changes.
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push((arg, positive));
                    }
                }
                TermData::Ite(c, t, e) => {
                    // ITE: condition is non-polar, branches inherit.
                    stack.push((*c, true));
                    stack.push((*c, false));
                    stack.push((*t, positive));
                    stack.push((*e, positive));
                }
                _ => {}
            }
        }

        // Axiom: combined multi-contains length lower bounds (#3982).
        //
        // For each variable x with 2+ positive str.contains(x, c_i) where c_i
        // are distinct string constants, emit pairwise:
        //   (AND contains(x, c1) contains(x, c2)) => len(x) >= min_combined_len(c1, c2)
        //
        // min_combined_len accounts for potential overlap: the maximum suffix of
        // c1 that is a prefix of c2 (or vice versa) can be shared in x. Without
        // this, the LIA solver only sees individual len(x) >= len(c_i) bounds,
        // which are insufficient when len(c1) + len(c2) - overlap > len(x).
        //
        // Example: contains(x,"ab") AND contains(x,"cd") AND len(x)=3
        //   Individual: len(x) >= 2 (ok with len(x)=3)
        //   Combined: len(x) >= 4 (contradicts len(x)=3 → UNSAT)
        for (&haystack_var, atoms) in &const_contains_by_var {
            if atoms.len() < 2 {
                continue;
            }
            // Emit pairwise bounds for each distinct pair.
            for i in 0..atoms.len() {
                for j in (i + 1)..atoms.len() {
                    let (pred1, ref s1) = atoms[i];
                    let (pred2, ref s2) = atoms[j];

                    let min_combined = multi_contains_min_len(s1, s2);

                    // Only emit if the combined bound is strictly tighter than
                    // the maximum individual bound. Otherwise Axiom 7 already
                    // covers it.
                    let max_individual = s1.chars().count().max(s2.chars().count());
                    if min_combined <= max_individual {
                        continue;
                    }

                    let len_x = self.ctx.terms.mk_app(
                        Symbol::named("str.len"),
                        vec![haystack_var],
                        Sort::Int,
                    );
                    let bound = self.ctx.terms.mk_int(BigInt::from(min_combined));
                    let ge = self.ctx.terms.mk_ge(len_x, bound);
                    // Guard: (AND pred1 pred2) => len(x) >= combined
                    let conj = self.ctx.terms.mk_and(vec![pred1, pred2]);
                    let implies = self.ctx.terms.mk_implies(conj, ge);
                    decompositions.push(implies);
                }
            }
        }

        decompositions
    }
}
