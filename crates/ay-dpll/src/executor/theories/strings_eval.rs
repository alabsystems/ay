// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground string evaluation helpers.
//!
//! Syntactic ground evaluation of string-sorted and integer-sorted terms
//! using only term-store constants (no solver state needed).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::Executor;

impl Executor {
    /// Returns true if `term` is syntactically fixed to a concrete string.
    ///
    /// A `str.++` is ground when every leaf component is itself ground (a
    /// string constant or a variable fixed to a constant by a top-level
    /// equality). This lets positive `str.contains`/`prefixof`/`suffixof`
    /// over a concat whose operands are all fixed (e.g. `(str.++ x y)` with
    /// `x = "ab"`, `y = "cd"`) be evaluated directly by `eval_contains`
    /// instead of being skolem-decomposed, which the CEGAR loop cannot close
    /// when every operand is a variable (the decomposition stalls). Direct
    /// evaluation on the fully-determined value is both sound and complete.
    pub(super) fn term_has_ground_string_value(
        &self,
        ground_string_terms: &HashSet<TermId>,
        term: TermId,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(_)) => true,
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                let args: Vec<TermId> = args.clone();
                !args.is_empty()
                    && args
                        .iter()
                        .all(|&a| self.term_has_ground_string_value(ground_string_terms, a))
            }
            _ => ground_string_terms.contains(&term),
        }
    }

    /// Collect terms that are fixed to a single string constant by top-level
    /// conjunction equalities in `assertions`.
    pub(super) fn collect_top_level_ground_string_terms(
        &self,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        let mut eq_graph: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut eq_nodes: HashSet<TermId> = HashSet::default();

        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack.pop() {
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];
                    if *self.ctx.terms.sort(lhs) == Sort::String
                        && *self.ctx.terms.sort(rhs) == Sort::String
                    {
                        eq_graph.entry(lhs).or_default().push(rhs);
                        eq_graph.entry(rhs).or_default().push(lhs);
                        eq_nodes.insert(lhs);
                        eq_nodes.insert(rhs);
                    }
                }
                _ => {}
            }
        }

        let mut ground_terms = HashSet::default();
        let mut visited = HashSet::default();

        for &root in &eq_nodes {
            if !visited.insert(root) {
                continue;
            }

            let mut component = Vec::new();
            let mut component_stack = vec![root];
            let mut unique_constant: Option<TermId> = None;
            let mut has_conflicting_constants = false;

            while let Some(current) = component_stack.pop() {
                component.push(current);

                if let TermData::Const(Constant::String(_)) = self.ctx.terms.get(current) {
                    if let Some(existing) = unique_constant {
                        if existing != current {
                            has_conflicting_constants = true;
                        }
                    } else {
                        unique_constant = Some(current);
                    }
                }

                if let Some(neighbors) = eq_graph.get(&current) {
                    for &next in neighbors {
                        if visited.insert(next) {
                            component_stack.push(next);
                        }
                    }
                }
            }

            if unique_constant.is_some() && !has_conflicting_constants {
                ground_terms.extend(component);
            }
        }

        ground_terms
    }

    /// Build an index mapping each term to the set of concat leaf components
    /// it is syntactically equated to in the assertions.
    pub(super) fn build_concat_component_index(
        &self,
        assertions: &[TermId],
    ) -> HashMap<TermId, HashSet<TermId>> {
        let mut index: HashMap<TermId, HashSet<TermId>> = HashMap::default();
        for &a in assertions {
            let mut eq_stack = vec![a];
            while let Some(t) = eq_stack.pop() {
                match self.ctx.terms.get(t) {
                    TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                        let lhs = args[0];
                        let rhs = args[1];
                        let mut lhs_leaves = Vec::new();
                        Self::collect_concat_leaves(&self.ctx.terms, lhs, &mut lhs_leaves);
                        if lhs_leaves.len() > 1 {
                            let set: HashSet<TermId> = lhs_leaves.iter().copied().collect();
                            index.entry(rhs).or_default().extend(&set);
                            index.entry(lhs).or_default().extend(&set);
                        }
                        let mut rhs_leaves = Vec::new();
                        Self::collect_concat_leaves(&self.ctx.terms, rhs, &mut rhs_leaves);
                        if rhs_leaves.len() > 1 {
                            let set: HashSet<TermId> = rhs_leaves.iter().copied().collect();
                            index.entry(lhs).or_default().extend(&set);
                            index.entry(rhs).or_default().extend(&set);
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "and" => {
                        for &arg in args.iter() {
                            eq_stack.push(arg);
                        }
                    }
                    _ => {}
                }
            }
        }
        index
    }

    /// Collect leaf components of a syntactic concat term.
    pub(super) fn collect_concat_leaves(
        terms: &ay_core::TermStore,
        t: TermId,
        out: &mut Vec<TermId>,
    ) {
        match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "str.++" => {
                for &arg in args {
                    Self::collect_concat_leaves(terms, arg, out);
                }
            }
            _ => out.push(t),
        }
    }

    /// Check if `needle` appears as a syntactic component of `haystack`'s
    /// concat structure (using the pre-built component index).
    pub(super) fn needle_in_concat_components(
        concat_components: &HashMap<TermId, HashSet<TermId>>,
        terms: &ay_core::TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let Some(components) = concat_components.get(&haystack) else {
            return false;
        };
        // Direct match: needle term is a component.
        if components.contains(&needle) {
            return true;
        }
        // Constant substring match: if needle is a string constant, check if
        // any constant component contains it.
        if let TermData::Const(Constant::String(needle_str)) = terms.get(needle) {
            for &comp in components {
                if let TermData::Const(Constant::String(comp_str)) = terms.get(comp) {
                    if comp_str.contains(needle_str.as_str()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Inline String variables that a TOP-LEVEL conjunct fixes to a string
    /// literal (`(= v "lit")` / `(= "lit" v)`), substituting the literal for
    /// every occurrence of `v` across all assertions.
    ///
    /// Motivation (#mix-str2int-array-index): a string→Int op over such a
    /// variable — `(str.to_int s)`, `(str.indexof s ...)`, `(str.len s)`,
    /// `(str.to_code s)` — is opaque to the combined array/EUF/LIA solver, which
    /// only sees the eager range axiom `str.to_int(s) >= -1`. When that op is
    /// used as an ARRAY INDEX (e.g. `(select a (str.to_int s))` with `s = ""`,
    /// so `str.to_int(s) = -1`), the index value never reaches the select
    /// congruence, so `(select a (str.to_int s))` and `(select a (- 1))` are not
    /// unified and a contradictory pair of assignments is wrongly satisfiable.
    /// Substituting `s := ""` makes the op ground (`(str.to_int "")`), which the
    /// subsequent `fold_ground_string_ops` pass folds to its concrete value,
    /// after which the two selects share an index and EUF refutes the conflict.
    ///
    /// SOUND/equisatisfiable: `v` is asserted equal to the literal, so every
    /// satisfying model maps `v` to that exact string; replacing `v` by the
    /// literal preserves the truth value of every assertion. The defining
    /// equality `(= v lit)` itself is KEPT VERBATIM (substituting inside it
    /// would collapse it to `(= lit lit)`, erasing `v` from the formula
    /// entirely — the theory solver then never binds `v`, model validation
    /// runs on assertions that no longer mention `v`, and the printed model
    /// falls back to the unconstrained-String default `""`, violating the
    /// user's own assertion: the `sv = "" for (= sv "xyz")` wrong-model bug).
    /// A binding mined from a NESTED conjunct (inside `and`) or derived from
    /// `(= (str.len v) 0)` has no top-level equality to keep, so the binding
    /// is re-asserted as a fresh top-level `(= v lit)` — implied by the
    /// original assertion, hence equivalence-preserving. If a variable is
    /// fixed to two DIFFERENT literals the formula is already unsatisfiable;
    /// we skip such variables and leave the conflicting equalities for EUF to
    /// refute.
    ///
    /// Only literal-valued string equalities are inlined (capture-free: literals
    /// contain no variables), and only when the bound side is a plain `Var`.
    pub(in crate::executor) fn inline_determined_string_vars(
        &mut self,
        assertions: &[TermId],
    ) -> Vec<TermId> {
        use super::super::proof_resolution::congruence::substitute_in_term;

        // Collect (var, literal) bindings from top-level conjunct equalities.
        let mut binding: HashMap<TermId, TermId> = HashMap::default();
        let mut conflicted: HashSet<TermId> = HashSet::default();
        let mut conjuncts: Vec<TermId> = Vec::new();
        for &a in assertions {
            // The assertion itself is a top-level conjunct (a bare `(= s "")` is
            // not wrapped in `and`); `collect_and_conjuncts` only descends into
            // `and` nodes, so seed with `a` and let it add nested conjuncts.
            conjuncts.push(a);
            crate::executor::quantifier_loop::collect_and_conjuncts(
                &self.ctx.terms,
                a,
                &mut conjuncts,
            );
        }
        for &c in &conjuncts {
            let mut found: Option<(TermId, TermId)> = None;
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(c) {
                if name == "=" && args.len() == 2 {
                    let (l, r) = (args[0], args[1]);
                    let is_str_var = |v: TermId| -> bool {
                        matches!(self.ctx.terms.get(v), TermData::Var(_, _))
                            && *self.ctx.terms.sort(v) == Sort::String
                    };
                    let as_str_lit = |t: TermId| -> Option<TermId> {
                        if matches!(self.ctx.terms.get(t), TermData::Const(Constant::String(_))) {
                            Some(t)
                        } else {
                            None
                        }
                    };
                    // `str.len v` term wrapping a string Var.
                    let len_var = |t: TermId| -> Option<TermId> {
                        if let TermData::App(Symbol::Named(n), a) = self.ctx.terms.get(t) {
                            if n == "str.len" && a.len() == 1 && is_str_var(a[0]) {
                                return Some(a[0]);
                            }
                        }
                        None
                    };
                    let is_zero = |t: TermId| -> bool {
                        matches!(self.ctx.terms.get(t),
                            TermData::Const(Constant::Int(n)) if *n == BigInt::from(0))
                    };
                    // Case 1: `(= v "lit")` / `(= "lit" v)` — bind v := lit.
                    if is_str_var(l) {
                        if let Some(lit) = as_str_lit(r) {
                            found = Some((l, lit));
                        }
                    }
                    if found.is_none() && is_str_var(r) {
                        if let Some(lit) = as_str_lit(l) {
                            found = Some((r, lit));
                        }
                    }
                    // Case 2: `(= (str.len v) 0)` / `(= 0 (str.len v))` — v is "".
                    // `str.len(v) = 0  <=>  v = ""` (SMT-LIB), so v is determined
                    // empty; bind v := "". Covers the derived form where the
                    // problem constrains the length rather than naming the literal.
                    if found.is_none() {
                        if let Some(v) = len_var(l).filter(|_| is_zero(r)) {
                            found = Some((v, self.ctx.terms.mk_string(String::new())));
                        } else if let Some(v) = len_var(r).filter(|_| is_zero(l)) {
                            found = Some((v, self.ctx.terms.mk_string(String::new())));
                        }
                    }
                }
            }
            if let Some((v, lit)) = found {
                match binding.get(&v) {
                    Some(&prev) if prev != lit => {
                        conflicted.insert(v);
                    }
                    _ => {
                        binding.insert(v, lit);
                    }
                }
            }
        }
        for v in &conflicted {
            binding.remove(v);
        }
        if binding.is_empty() {
            return assertions.to_vec();
        }

        let pairs: Vec<(TermId, TermId)> = binding.into_iter().collect();

        // A top-level assertion that IS a defining equality `(= v lit)` /
        // `(= lit v)` for one of the bindings must survive UNSUBSTITUTED: it
        // is the only assertion binding `v`, and rewriting it would erase `v`
        // from the formula (see doc comment). Everything else gets the full
        // substitution.
        let is_defining_equality = |terms: &ay_core::TermStore, t: TermId| -> bool {
            if let TermData::App(Symbol::Named(name), args) = terms.get(t) {
                if name == "=" && args.len() == 2 {
                    return pairs.iter().any(|&(v, lit)| {
                        (args[0] == v && args[1] == lit) || (args[0] == lit && args[1] == v)
                    });
                }
            }
            false
        };
        let mut preserved: HashSet<TermId> = HashSet::default();
        let mut out: Vec<TermId> = assertions
            .iter()
            .map(|&t| {
                if is_defining_equality(&self.ctx.terms, t) {
                    preserved.insert(t);
                    return t;
                }
                let mut cur = t;
                for &(from, to) in &pairs {
                    cur = substitute_in_term(&mut self.ctx.terms, cur, from, to);
                }
                cur
            })
            .collect();

        // Re-assert bindings whose defining equality was NOT preserved at the
        // top level (mined from a nested `and` conjunct, or derived from
        // `(= (str.len v) 0)`). Without this the substitution above removed
        // every occurrence of `v`, unbinding it exactly like the collapsed
        // top-level case.
        for &(v, lit) in &pairs {
            let kept = preserved.iter().any(|&t| {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                    name == "="
                        && args.len() == 2
                        && ((args[0] == v && args[1] == lit) || (args[0] == lit && args[1] == v))
                } else {
                    false
                }
            });
            if !kept {
                let eq = self.ctx.terms.mk_eq(v, lit);
                if !out.contains(&eq) {
                    out.push(eq);
                }
            }
        }
        out
    }

    /// Fold fully-ground string operations to constants pre-Tseitin.
    ///
    /// Walks each assertion's DAG bottom-up: when a string operation has all
    /// constant arguments, evaluate it and replace the term with the result.
    /// This eliminates ground computation from the SAT encoding.
    pub(in crate::executor) fn fold_ground_string_ops(
        &mut self,
        assertions: &[TermId],
    ) -> Vec<TermId> {
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        assertions
            .iter()
            .map(|&t| self.rewrite_ground_string_ops(t, &mut cache))
            .collect()
    }

    fn rewrite_ground_string_ops(
        &mut self,
        term: TermId,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
        let result = match self.ctx.terms.get(term).clone() {
            TermData::App(ref sym, ref args) if !args.is_empty() => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.rewrite_ground_string_ops(a, cache))
                    .collect();
                let changed = new_args.iter().zip(args.iter()).any(|(a, b)| a != b);
                let rebuilt = if changed {
                    // Use mk_eq for equality nodes so constant-folding fires
                    if sym.name() == "=" && new_args.len() == 2 {
                        self.ctx.terms.mk_eq(new_args[0], new_args[1])
                    } else {
                        self.ctx.terms.mk_app(
                            sym.clone(),
                            new_args,
                            self.ctx.terms.sort(term).clone(),
                        )
                    }
                } else {
                    term
                };
                // Try to evaluate the rebuilt term if it's now ground
                self.fold_ground_evaluated_term(rebuilt)
            }
            TermData::Not(inner) => {
                let new_inner = self.rewrite_ground_string_ops(inner, cache);
                if new_inner != inner {
                    self.ctx.terms.mk_not(new_inner)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.rewrite_ground_string_ops(c, cache);
                let nt = self.rewrite_ground_string_ops(t, cache);
                let ne = self.rewrite_ground_string_ops(e, cache);
                if nc != c || nt != t || ne != e {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            _ => term,
        };
        cache.insert(term, result);
        result
    }

    fn fold_ground_evaluated_term(&mut self, term: TermId) -> TermId {
        // Provably-empty substr: `(str.substr s i n)` with CONSTANT `i < 0` or
        // `n <= 0` is "" per SMT-LIB regardless of `s`, so fold even when `s` is
        // non-ground (e.g. a `(select a j)` string). Mirrors the seq.extract empty
        // fold; lets `(str.len (str.++ (str.substr (select a j) -1 0) "hiz")) = 2`
        // resolve `len = 3 != 2` in a mixed string+array problem (#mix-substr-empty).
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
            if name == "str.substr" && args.len() == 3 {
                let neg_start = matches!(
                    self.ctx.terms.get(args[1]),
                    TermData::Const(Constant::Int(i)) if *i < BigInt::from(0)
                );
                let nonpos_len = matches!(
                    self.ctx.terms.get(args[2]),
                    TermData::Const(Constant::Int(n)) if *n <= BigInt::from(0)
                );
                if neg_start || nonpos_len {
                    return self.ctx.terms.mk_string(String::new());
                }
            }
            // Empty-pattern replace: `(str.replace x "" r) = (str.++ r x)` for ANY
            // `x` (the empty pattern always matches at position 0, so `r` is
            // inserted at the front), and `= x` when `r` is also `""`. Folding even
            // when `x` is non-ground links `(str.len (str.replace x "" ""))` to
            // `(str.len x)` via the concat-length axiom, so a mixed string+array
            // problem using it as an array index can no longer leave the length
            // opaque (#mix-str2int-array-index, combo_all_4). Verified vs z3:
            // `replace x "" r = r ++ x` is a tautology.
            if name == "str.replace" && args.len() == 3 {
                let pat_empty = matches!(
                    self.ctx.terms.get(args[1]),
                    TermData::Const(Constant::String(p)) if p.is_empty()
                );
                if pat_empty {
                    let r_empty = matches!(
                        self.ctx.terms.get(args[2]),
                        TermData::Const(Constant::String(r)) if r.is_empty()
                    );
                    let x = args[0];
                    let r = args[2];
                    if r_empty {
                        return x;
                    }
                    return self.ctx.terms.mk_app(
                        Symbol::named("str.++"),
                        vec![r, x],
                        Sort::String,
                    );
                }
            }
            // Drop empty-literal operands from a concat: `(str.++ "" x) = x`,
            // `(str.++ x "" y) = (str.++ x y)`. The empty string is the identity
            // of `str.++`, so this is a tautology. Folding even when operands are
            // non-ground collapses `(str.to_int (str.++ "" s))` to `(str.to_int s)`,
            // so a string→Int op over such a concat used as an array index reaches
            // the select congruence (#mix-str2int-array-index). A single remaining
            // operand replaces the concat; an all-empty concat folds to "".
            if name == "str.++" && args.len() >= 2 {
                let is_empty_lit = |t: TermId| {
                    matches!(self.ctx.terms.get(t),
                        TermData::Const(Constant::String(p)) if p.is_empty())
                };
                if args.iter().any(|&t| is_empty_lit(t)) {
                    let kept: Vec<TermId> =
                        args.iter().copied().filter(|&t| !is_empty_lit(t)).collect();
                    return match kept.len() {
                        0 => self.ctx.terms.mk_string(String::new()),
                        1 => kept[0],
                        _ => self
                            .ctx
                            .terms
                            .mk_app(Symbol::named("str.++"), kept, Sort::String),
                    };
                }
            }
        }
        // Try string evaluation
        if let Some(s) = ground_eval_string_term(&self.ctx.terms, term) {
            return self.ctx.terms.mk_string(s);
        }
        // Try int evaluation (str.len, str.indexof, etc.)
        if let Some(i) = ground_eval_int_term(&self.ctx.terms, term) {
            return self.ctx.terms.mk_int(i);
        }
        // Try bool evaluation (str.contains, str.prefixof, etc.)
        if let Some(b) = self.ground_eval_bool_term(term) {
            return self.ctx.terms.mk_bool(b);
        }
        term
    }

    fn ground_eval_bool_term(&self, term: TermId) -> Option<bool> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "str.contains" if args.len() == 2 => {
                    let s = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let t = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.contains(&*t))
                }
                "str.prefixof" if args.len() == 2 => {
                    let p = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let s = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.starts_with(&*p))
                }
                "str.suffixof" if args.len() == 2 => {
                    let suf = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    let s = ground_eval_string_term(&self.ctx.terms, args[1])?;
                    Some(s.ends_with(&*suf))
                }
                "str.is_digit" if args.len() == 1 => {
                    let s = ground_eval_string_term(&self.ctx.terms, args[0])?;
                    Some(s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit()))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Syntactic ground evaluation of a string-sorted term.
///
/// Returns `Some(s)` if the term can be fully evaluated to a concrete string
/// using only syntactic constants in the term store (no EQC lookup, no solver
/// state). This handles the case where extended functions like `str.replace`
/// appear inside `str.len` with all-constant arguments.
///
/// CVC5 reference: `extf_solver.cpp:295-530` (partial evaluation pipeline).
pub(super) fn ground_eval_string_term(terms: &ay_core::TermStore, t: TermId) -> Option<String> {
    match terms.get(t) {
        TermData::Const(Constant::String(s)) => Some(s.clone()),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "str.++" => {
                let mut result = String::new();
                for &arg in args {
                    result.push_str(&ground_eval_string_term(terms, arg)?);
                }
                Some(result)
            }
            "str.replace" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let pattern = ground_eval_string_term(terms, args[1])?;
                let replacement = ground_eval_string_term(terms, args[2])?;
                if pattern.is_empty() {
                    let mut r = replacement;
                    r.push_str(&s);
                    Some(r)
                } else {
                    match s.find(&*pattern) {
                        Some(pos) => {
                            let mut r = s[..pos].to_string();
                            r.push_str(&replacement);
                            r.push_str(&s[pos + pattern.len()..]);
                            Some(r)
                        }
                        None => Some(s),
                    }
                }
            }
            "str.replace_all" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let pattern = ground_eval_string_term(terms, args[1])?;
                let replacement = ground_eval_string_term(terms, args[2])?;
                if pattern.is_empty() {
                    Some(s)
                } else {
                    Some(s.replace(&*pattern, &replacement))
                }
            }
            "str.substr" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let start = ground_eval_int_term(terms, args[1])?;
                let len = ground_eval_int_term(terms, args[2])?;
                eval_substr(&s, &start, &len)
            }
            "str.at" if args.len() == 2 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let i = ground_eval_int_term(terms, args[1])?;
                eval_str_at(&s, &i)
            }
            "str.from_int" | "int.to.str" if args.len() == 1 => {
                let n = ground_eval_int_term(terms, args[0])?;
                if n < BigInt::from(0) {
                    Some(String::new())
                } else {
                    Some(n.to_string())
                }
            }
            "str.from_code" if args.len() == 1 => {
                let n = ground_eval_int_term(terms, args[0])?;
                let code: i64 = n.try_into().ok()?;
                if !(0..=196_607).contains(&code) {
                    Some(String::new())
                } else {
                    char::from_u32(code as u32)
                        .map(|c| c.to_string())
                        .or(Some(String::new()))
                }
            }
            "str.to_lower" if args.len() == 1 => {
                let s = ground_eval_string_term(terms, args[0])?;
                Some(s.to_lowercase())
            }
            "str.to_upper" if args.len() == 1 => {
                let s = ground_eval_string_term(terms, args[0])?;
                Some(s.to_uppercase())
            }
            "str.replace_re" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let t = ground_eval_string_term(terms, args[2])?;
                // args[1] is a RegLan term — evaluate structurally.
                ay_strings::ground_eval_replace_re(terms, &s, args[1], &t)
            }
            "str.replace_re_all" if args.len() == 3 => {
                let s = ground_eval_string_term(terms, args[0])?;
                let t = ground_eval_string_term(terms, args[2])?;
                ay_strings::ground_eval_replace_re_all(terms, &s, args[1], &t)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Syntactic ground evaluation of an integer-sorted term.
///
/// Returns `Some(n)` if the term is a syntactic integer constant.
/// Does not handle arithmetic expressions — only literal constants.
pub(super) fn ground_eval_int_term(terms: &ay_core::TermStore, t: TermId) -> Option<BigInt> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(n.clone()),
        // Handle negation: (- n) where n is a positive constant.
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            let inner = ground_eval_int_term(terms, args[0])?;
            Some(-inner)
        }
        TermData::App(Symbol::Named(name), args) if name == "str.len" && args.len() == 1 => {
            let s = ground_eval_string_term(terms, args[0])?;
            Some(BigInt::from(s.chars().count()))
        }
        TermData::App(Symbol::Named(name), args) if name == "str.indexof" && args.len() == 3 => {
            let s = ground_eval_string_term(terms, args[0])?;
            let t = ground_eval_string_term(terms, args[1])?;
            let start = ground_eval_int_term(terms, args[2])?;
            Some(
                ay_strings::eval::eval_str_indexof(&s, &t, &start)
                    .unwrap_or_else(|| BigInt::from(-1)),
            )
        }
        TermData::App(Symbol::Named(name), args) if name == "str.to_code" && args.len() == 1 => {
            let s = ground_eval_string_term(terms, args[0])?;
            let mut chars = s.chars();
            match (chars.next(), chars.next()) {
                (Some(c), None) if (c as u32) <= 196_607 => Some(BigInt::from(c as u32)),
                _ => Some(BigInt::from(-1)),
            }
        }
        TermData::App(Symbol::Named(name), args) if name == "str.to_int" && args.len() == 1 => {
            let s = ground_eval_string_term(terms, args[0])?;
            if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
                Some(BigInt::from(-1))
            } else {
                s.parse::<BigInt>().ok()
            }
        }
        _ => None,
    }
}

/// SMT-LIB `str.substr(s, start, len)` with ground arguments.
pub(super) fn eval_substr(s: &str, start: &BigInt, len: &BigInt) -> Option<String> {
    let zero = BigInt::from(0);
    if *start < zero || *len <= zero {
        return Some(String::new());
    }
    let start_usize: usize = start.try_into().ok()?;
    let len_usize: usize = len.try_into().ok()?;
    let chars: Vec<char> = s.chars().collect();
    if start_usize >= chars.len() {
        return Some(String::new());
    }
    debug_assert!(
        start_usize.checked_add(len_usize).is_some(),
        "BUG: eval_substr overflow: start {start_usize} + len {len_usize} overflows usize"
    );
    let end = std::cmp::min(start_usize + len_usize, chars.len());
    Some(chars[start_usize..end].iter().collect())
}

/// SMT-LIB `str.at(s, i)` with ground arguments.
pub(super) fn eval_str_at(s: &str, i: &BigInt) -> Option<String> {
    let zero = BigInt::from(0);
    if *i < zero {
        return Some(String::new());
    }
    let idx: usize = i.try_into().ok()?;
    let chars: Vec<char> = s.chars().collect();
    if idx >= chars.len() {
        Some(String::new())
    } else {
        Some(chars[idx].to_string())
    }
}

/// Compute the minimum length a string must have to contain both `s1` and `s2`.
///
/// The two patterns may overlap in x: a suffix of one can be a prefix of the
/// other, reducing the combined footprint. The minimum combined length is:
///   `len(s1) + len(s2) - max_suffix_prefix_overlap(s1, s2)`
///
/// where `max_suffix_prefix_overlap(a, b)` is `max(spo(a,b), spo(b,a))` and
/// `spo(a, b)` is the length of the longest suffix of `a` that is a prefix of `b`.
///
/// Example: "ab" and "cd" → overlap 0 → min len 4
/// Example: "ab" and "bc" → overlap 1 → min len 3
/// Example: "abc" and "abc" → overlap 3 → min len 3
pub(super) fn multi_contains_min_len(s1: &str, s2: &str) -> usize {
    let len1 = s1.chars().count();
    let len2 = s2.chars().count();
    let overlap = suffix_prefix_overlap(s1, s2).max(suffix_prefix_overlap(s2, s1));
    len1 + len2 - overlap
}

/// Length of the longest suffix of `a` that is a prefix of `b`.
pub(super) fn suffix_prefix_overlap(a: &str, b: &str) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let max_check = a_chars.len().min(b_chars.len());
    for overlap in (1..=max_check).rev() {
        if a_chars[a_chars.len() - overlap..] == b_chars[..overlap] {
            return overlap;
        }
    }
    0
}

#[cfg(test)]
mod tests;
