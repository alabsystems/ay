// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String-length axiom collection from term roots.
//!
//! Generates non-negativity, zero-length/empty biconditional, concat
//! decomposition, containment length bounds, range-restricted function
//! bounds, and ground extended-function equality axioms.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::strings_eval::ground_eval_string_term;

impl Executor {
    /// Collect str.len terms from all active assertions and generate length axioms.
    pub(in crate::executor) fn collect_str_len_axioms(&mut self) -> Vec<TermId> {
        let roots = self.ctx.assertions.clone();
        self.collect_str_len_axioms_from_roots(&roots)
    }

    /// Collect `str.substr` terms from all active assertions and emit length
    /// UPPER-BOUND axioms.
    ///
    /// SMT-LIB `(str.substr s i n)` is the longest substring of `s` starting at
    /// position `i` of length at most `n` when `0 <= i < len(s)` and `0 <= n`,
    /// and `""` otherwise. The pure-string normal-form solver derives these
    /// bounds during reduction, but a MIXED string+array/UF problem dispatches to
    /// a combined solver that treats `str.len(str.substr ...)` as an
    /// uninterpreted non-negative integer, so a conjunct like
    /// `(= (str.len (str.substr (select a 0) 0 2)) 4)` is wrongly satisfiable
    /// (a length-2-bounded substring can never have length 4).
    ///
    /// For every `(str.substr s i n)` subterm, with `L = (str.len (str.substr s i n))`:
    /// 1. `(>= L 0)`                                  — non-negativity
    /// 2. `(<= L (str.len s))`                         — substring is no longer than source
    /// 3. `(or (= L 0) (<= (+ L i) (str.len s)))`      — a non-empty substring at offset `i`
    ///    fits within `[i, len(s))`, so `i + L <= len(s)`; otherwise it is empty
    /// 4. `(<= L n)` when `n` is an integer constant `>= 0` — bounded by the requested length
    /// 5. the EXACT length equation `L = max(0, min(n, len(s) - i))` (guarded for
    ///    out-of-range `i`/`n`), which also supplies the LOWER bound so e.g.
    ///    `(str.substr (str.++ x "hi") 0 3)` cannot have length 0
    ///
    /// Every axiom is implied by the SMT-LIB semantics (sound for ALL `i`/`n`:
    /// negative or out-of-range arguments yield the empty result, satisfying the
    /// `(= L 0)` disjunct and the `n >= 0` guard), so this can only ADD refutation
    /// power — never manufacture a wrong-UNSAT.
    pub(in crate::executor) fn collect_substr_len_bound_axioms(&mut self) -> Vec<TermId> {
        let roots = self.ctx.assertions.clone();
        // (substr_term, s, i, n)
        let mut substrs: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        let mut seen_substr: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots;
        let mut visited: HashSet<TermId> = HashSet::default();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.substr" && args.len() == 3 && seen_substr.insert(term) {
                        substrs.push((term, args[0], args[1], args[2]));
                    }
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    let binding_vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                    let body_id = *body;
                    for val in binding_vals {
                        stack.push(val);
                    }
                    stack.push(body_id);
                }
                _ => {}
            }
        }

        let mut axioms = Vec::new();
        // `str.len(s)` terms for each substr source. These are freshly created and
        // may wrap a `str.++` concat or string literal whose length the combined
        // solver has not otherwise decomposed (e.g. the source
        // `(str.++ (select a j) "hi")` has length `>= 2`). After the main loop we
        // feed these through `collect_str_len_axioms_from_roots` to emit the
        // concat-sum / constant-fold length facts, without which the exact substr
        // length equation below would leave `len(s)` unconstrained.
        let mut source_len_terms: Vec<TermId> = Vec::new();
        for (substr_term, s, i, n) in substrs {
            let len_substr =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![substr_term], Sort::Int);
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            source_len_terms.push(len_s);

            // 1. (>= L 0)
            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            axioms.push(self.ctx.terms.mk_ge(len_substr, zero));

            // 2. (<= L (str.len s))
            axioms.push(self.ctx.terms.mk_le(len_substr, len_s));

            // 3. (or (= L 0) (<= (+ L i) (str.len s)))
            let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
            let l_is_zero = self.ctx.terms.mk_eq(len_substr, zero3);
            let l_plus_i = self.ctx.terms.mk_add(vec![len_substr, i]);
            let fits = self.ctx.terms.mk_le(l_plus_i, len_s);
            axioms.push(self.ctx.terms.mk_or(vec![l_is_zero, fits]));

            // 4. (<= L n) when n is an integer constant >= 0
            if let TermData::Const(Constant::Int(nv)) = self.ctx.terms.get(n) {
                if *nv >= BigInt::from(0) {
                    let n_copy = n;
                    axioms.push(self.ctx.terms.mk_le(len_substr, n_copy));
                }
            }

            // 5. EXACT length equation (subsumes the bounds above; also supplies a
            //    LOWER bound, e.g. `(str.substr (str.++ x "hi") 0 3)` has length
            //    >= 2 so it can never be 0). Per SMT-LIB:
            //      L = max(0, min(n, len(s) - i))  when  0 <= i <= len(s) and n >= 0
            //      L = 0                            otherwise (i out of range or n < 0)
            //    Encoded with nested ITEs:
            //      (= L (ite (and (>= i 0) (<= i len_s) (>= n 0))
            //                (ite (<= (+ i n) len_s) n (- len_s i))
            //                0))
            //    This is the exact semantics — sound (cannot create wrong-UNSAT)
            //    and complete for ground i/n. The linear bounds above remain as
            //    cheap direct facts for the arithmetic solver.
            let zero_i = self.ctx.terms.mk_int(BigInt::from(0));
            let i_nonneg = self.ctx.terms.mk_ge(i, zero_i);
            let i_le_len = self.ctx.terms.mk_le(i, len_s);
            let zero_n = self.ctx.terms.mk_int(BigInt::from(0));
            let n_nonneg = self.ctx.terms.mk_ge(n, zero_n);
            let in_range = self.ctx.terms.mk_and(vec![i_nonneg, i_le_len, n_nonneg]);

            let i_plus_n = self.ctx.terms.mk_add(vec![i, n]);
            let fits_n = self.ctx.terms.mk_le(i_plus_n, len_s);
            let len_minus_i = self.ctx.terms.mk_sub(vec![len_s, i]);
            let inner_ite = self.ctx.terms.mk_ite(fits_n, n, len_minus_i);

            let zero_else = self.ctx.terms.mk_int(BigInt::from(0));
            let exact = self.ctx.terms.mk_ite(in_range, inner_ite, zero_else);
            let eq = self.ctx.terms.mk_eq(len_substr, exact);
            axioms.push(eq);
        }

        // Decompose the source lengths (concat-sum + constant folding) so the
        // exact substr equations above are not left with an unconstrained
        // `len(s)` when `s` is a literal or concat.
        if !source_len_terms.is_empty() {
            let source_axioms = self.collect_str_len_axioms_from_roots(&source_len_terms);
            axioms.extend(source_axioms);
        }

        axioms
    }

    /// Collect str.len terms from provided roots and generate length axioms.
    ///
    /// For each `str.len(x)` found, generates:
    /// 1. `(>= (str.len x) 0)` — non-negativity
    /// 2. `(=> (= (str.len x) 0) (= x ""))` — zero length implies empty
    /// 3. `(=> (= x "") (= (str.len x) 0))` — empty implies zero length
    ///
    /// For each `str.++(a, b)` where the concat appears under str.len:
    /// 4. `(= (str.len (str.++ a b)) (+ (str.len a) (str.len b)))` — concat decomposition
    ///
    /// For each `str.contains(x, s)` / `str.prefixof(s, x)` / `str.suffixof(s, x)`:
    /// 7. `(=> (str.contains x s) (>= (str.len x) (str.len s)))` — containment length bound
    ///
    /// For each range-restricted integer function (CVC5 `eagerReduce`):
    /// 9. `(>= (str.to_int x) (- 1))` — str.to_int lower bound
    /// 9. `(>= (str.to_code x) (- 1))`, `(<= (str.to_code x) 196607)` — str.to_code bounds
    /// 9. `(>= (str.indexof x y n) (- 1))` — str.indexof lower bound
    pub(in crate::executor) fn collect_str_len_axioms_from_roots(
        &mut self,
        roots: &[TermId],
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let mut seen_len_args: HashSet<TermId> = HashSet::default();
        let mut seen_concat_len: HashSet<TermId> = HashSet::default();

        // First pass: collect str.len terms (TermIds) without mutating the store.
        let mut str_len_terms: Vec<(TermId, TermId)> = Vec::new(); // (str.len(x), x)
        let mut concat_len_terms: Vec<(TermId, TermId, Vec<TermId>)> = Vec::new(); // (str.len(concat), concat, [args])
                                                                                   // Direct str.len of string constants: (str_len_term, char_count).
        let mut direct_const_len: Vec<(TermId, usize)> = Vec::new();
        // Concat arg constants: (concat_arg_term, char_count).
        let mut concat_arg_const_len: Vec<(TermId, usize)> = Vec::new();
        // Containment predicates: (predicate_term, container, contained).
        // str.contains(x, s) => container=x, contained=s
        // str.prefixof(s, x) => container=x, contained=s
        // str.suffixof(s, x) => container=x, contained=s
        let mut containment_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen_containment: HashSet<TermId> = HashSet::default();
        // String equalities: (eq_term, lhs, rhs) for (= lhs rhs) with String sort.
        let mut string_equalities: Vec<(TermId, TermId, TermId)> = Vec::new();
        // Range-restricted integer function applications.
        // Eager reduction lemmas (CVC5 term_registry.cpp:80-133): assert range
        // axioms at term registration so the LIA solver inherently rejects
        // out-of-range assignments.
        // Entry: (func_term, kind) where kind encodes the function type.
        // 0 = str.to_int (range: >= -1)
        // 1 = str.to_code (range: >= -1 AND <= 196607)
        // 2 = str.indexof (range: >= -1 AND <= str.len(x))
        let mut range_restricted_terms: Vec<(TermId, u8)> = Vec::new();
        let mut seen_range_restricted: HashSet<TermId> = HashSet::default();
        // Ground extf evaluations: (extf_term, evaluated_string).
        // When str.len wraps a ground extended function, we record both the
        // length axiom (via direct_const_len) and the ground equality
        // (extf_term = "result") so the string solver can merge the EQC.
        let mut ground_extf_evals: Vec<(TermId, String)> = Vec::new();

        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited: HashSet<TermId> = HashSet::default();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.len" && args.len() == 1 {
                        let inner = args[0];
                        if seen_len_args.insert(inner) {
                            str_len_terms.push((term, inner));
                        }
                        // Check inner term type.
                        match self.ctx.terms.get(inner) {
                            TermData::Const(Constant::String(s)) => {
                                // str.len of a string constant: record char count.
                                direct_const_len.push((term, s.chars().count()));
                            }
                            TermData::App(Symbol::Named(inner_name), inner_args)
                                if inner_name == "str.++"
                                    && inner_args.len() >= 2
                                    && seen_concat_len.insert(inner) =>
                            {
                                // Also check concat args for constants.
                                let cargs: Vec<TermId> = inner_args.clone();
                                for &carg in &cargs {
                                    if let TermData::Const(Constant::String(cs)) =
                                        self.ctx.terms.get(carg)
                                    {
                                        concat_arg_const_len.push((carg, cs.chars().count()));
                                    }
                                }
                                concat_len_terms.push((term, inner, cargs));
                            }
                            // Wave 0: Ground extf-in-length evaluation.
                            // When str.len wraps an extended function with all-constant
                            // arguments (e.g., str.len(str.replace("hello","ll","r"))),
                            // evaluate the inner function to a concrete string and emit
                            // both str.len(inner) = N AND inner = "result".
                            // The ground equality is needed so the string solver can
                            // merge the extf term with the constant and avoid setting
                            // incomplete=true in check_extf_reductions.
                            // CVC5 reference: extf_solver.cpp:295-530 (partial eval).
                            TermData::App(Symbol::Named(_), _) => {
                                if let Some(result) =
                                    ground_eval_string_term(&self.ctx.terms, inner)
                                {
                                    direct_const_len.push((term, result.chars().count()));
                                    ground_extf_evals.push((inner, result));
                                }
                            }
                            _ => {}
                        }
                    } else if name == "str.contains"
                        && args.len() == 2
                        && seen_containment.insert(term)
                    {
                        // str.contains(x, s): x is the container, s is the contained
                        containment_terms.push((term, args[0], args[1]));
                    } else if name == "str.prefixof"
                        && args.len() == 2
                        && seen_containment.insert(term)
                    {
                        // str.prefixof(s, x): s is prefix of x, so x is container
                        containment_terms.push((term, args[1], args[0]));
                    } else if name == "str.suffixof"
                        && args.len() == 2
                        && seen_containment.insert(term)
                    {
                        // str.suffixof(s, x): s is suffix of x, so x is container
                        containment_terms.push((term, args[1], args[0]));
                    } else if name == "=" && args.len() == 2 {
                        let lhs = args[0];
                        let rhs = args[1];
                        if *self.ctx.terms.sort(lhs) == Sort::String
                            && *self.ctx.terms.sort(rhs) == Sort::String
                        {
                            string_equalities.push((term, lhs, rhs));
                        }
                    }
                    // Detect range-restricted integer string functions for eager
                    // reduction lemmas (CVC5 term_registry eagerReduce).
                    if (name == "str.to_int" || name == "str.to.int")
                        && args.len() == 1
                        && seen_range_restricted.insert(term)
                    {
                        range_restricted_terms.push((term, 0));
                    } else if name == "str.to_code"
                        && args.len() == 1
                        && seen_range_restricted.insert(term)
                    {
                        range_restricted_terms.push((term, 1));
                    } else if name == "str.indexof"
                        && args.len() == 3
                        && seen_range_restricted.insert(term)
                    {
                        range_restricted_terms.push((term, 2));
                    }
                    // Wave 0b: Standalone ground extf evaluation.
                    // Ground extended function terms outside str.len wrappers
                    // must also be evaluated. Otherwise the solver never learns
                    // that e.g. str.at("hello", 0) = "h" and produces false SAT.
                    // CVC5 handles this at rewrite time (sequences_rewriter.cpp).
                    // Do NOT include str.++ — NF solver handles ground concats.
                    if matches!(
                        name.as_str(),
                        "str.at"
                            | "str.substr"
                            | "str.replace"
                            | "str.replace_all"
                            | "str.replace_re"
                            | "str.replace_re_all"
                            | "str.to_lower"
                            | "str.to_upper"
                            | "str.from_int"
                            | "int.to.str"
                            | "str.from_code"
                    ) {
                        if let Some(result) = ground_eval_string_term(&self.ctx.terms, term) {
                            ground_extf_evals.push((term, result));
                        }
                    }
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    let binding_vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                    let body_id = *body;
                    for val in binding_vals {
                        stack.push(val);
                    }
                    stack.push(body_id);
                }
                _ => {}
            }
        }

        // Second pass: generate axioms (now we can mutate the store).
        for (len_term, inner) in str_len_terms {
            // Axiom 1: str.len(x) >= 0
            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let ge = self.ctx.terms.mk_ge(len_term, zero);
            axioms.push(ge);

            // Axiom 2: str.len(x) = 0 => x = ""
            let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
            let len_eq_zero = self.ctx.terms.mk_eq(len_term, zero2);
            let empty = self.ctx.terms.mk_string(String::new());
            let x_eq_empty = self.ctx.terms.mk_eq(inner, empty);
            let implies_fwd = self.ctx.terms.mk_implies(len_eq_zero, x_eq_empty);
            axioms.push(implies_fwd);

            // Axiom 3: x = "" => str.len(x) = 0
            let empty2 = self.ctx.terms.mk_string(String::new());
            let x_eq_empty2 = self.ctx.terms.mk_eq(inner, empty2);
            let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
            let len_eq_zero2 = self.ctx.terms.mk_eq(len_term, zero3);
            let implies_rev = self.ctx.terms.mk_implies(x_eq_empty2, len_eq_zero2);
            axioms.push(implies_rev);
        }

        // Build a map of concat-arg constants for quick lookup.
        let concat_arg_map: HashMap<TermId, usize> = concat_arg_const_len.into_iter().collect();

        // Axiom 4: str.len(str.++(a,b,...)) = str.len(a) + str.len(b) + ...
        //
        // Decompose RECURSIVELY: a concat argument that is itself a `str.++`
        // (e.g. the inner `(str.++ (select a 2) "")` of
        // `(str.++ (str.++ (select a 2) "") (str.substr s0 0 2))`) is enqueued
        // and decomposed too, so its length is connected to its leaf operands.
        // Without this, the nested length stays opaque and a conjunct like
        // `(= (str.len <outer>) 0)` is wrongly satisfiable even when a leaf
        // operand has a known nonzero length.
        let mut concat_worklist: Vec<(TermId, Vec<TermId>)> = concat_len_terms
            .into_iter()
            .map(|(len_term, _concat, args)| (len_term, args))
            .collect();
        let mut decomposed: HashSet<TermId> = HashSet::default();
        while let Some((len_term, concat_args)) = concat_worklist.pop() {
            let len_parts: Vec<TermId> = concat_args
                .iter()
                .map(|&arg| {
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![arg], Sort::Int)
                })
                .collect();

            // For each concat argument, add non-negativity + zero-length ↔ empty axioms.
            for (i, &part) in len_parts.iter().enumerate() {
                let arg = concat_args[i];
                // Non-negativity: str.len(arg_i) >= 0
                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                let ge = self.ctx.terms.mk_ge(part, zero);
                axioms.push(ge);

                // str.len(arg_i) = 0 => arg_i = ""
                let zero_a = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(part, zero_a);
                let empty_a = self.ctx.terms.mk_string(String::new());
                let arg_eq_empty = self.ctx.terms.mk_eq(arg, empty_a);
                let fwd = self.ctx.terms.mk_implies(len_eq_zero, arg_eq_empty);
                axioms.push(fwd);

                // arg_i = "" => str.len(arg_i) = 0
                let empty_b = self.ctx.terms.mk_string(String::new());
                let arg_eq_empty2 = self.ctx.terms.mk_eq(arg, empty_b);
                let zero_b = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero2 = self.ctx.terms.mk_eq(part, zero_b);
                let rev = self.ctx.terms.mk_implies(arg_eq_empty2, len_eq_zero2);
                axioms.push(rev);
            }

            // Axiom 5: For each concat arg, fold a string-constant length
            // (str.len("abc") = 3) and ENQUEUE a nested concat for recursive
            // decomposition.
            for (i, &arg) in concat_args.iter().enumerate() {
                // Direct const length recorded in the first pass, or any string
                // literal we encounter at a nested level.
                let const_len =
                    concat_arg_map
                        .get(&arg)
                        .copied()
                        .or_else(|| match self.ctx.terms.get(arg) {
                            TermData::Const(Constant::String(s)) => Some(s.chars().count()),
                            _ => None,
                        });
                if let Some(char_count) = const_len {
                    let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
                    let const_eq = self.ctx.terms.mk_eq(len_parts[i], len_val);
                    axioms.push(const_eq);
                }

                if let TermData::App(Symbol::Named(n), inner_args) = self.ctx.terms.get(arg) {
                    if n == "str.++" && inner_args.len() >= 2 && decomposed.insert(arg) {
                        let inner_args: Vec<TermId> = inner_args.clone();
                        concat_worklist.push((len_parts[i], inner_args));
                    }
                }
            }

            let sum = self.ctx.terms.mk_add(len_parts);
            let eq = self.ctx.terms.mk_eq(len_term, sum);
            axioms.push(eq);
        }

        // Axiom 6: For direct str.len of string constants, str.len("abc") = 3
        // (term is the str.len application itself, not the inner constant)
        for (len_app, char_count) in direct_const_len {
            let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
            let const_eq = self.ctx.terms.mk_eq(len_app, len_val);
            axioms.push(const_eq);
        }

        // Axiom 7: Containment length bounds.
        // str.contains(x, s) => str.len(x) >= str.len(s)
        // str.prefixof(s, x) => str.len(x) >= str.len(s)
        // str.suffixof(s, x) => str.len(x) >= str.len(s)
        for (pred_term, container, contained) in containment_terms {
            let len_container =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![container], Sort::Int);
            let len_contained =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![contained], Sort::Int);

            // Non-negativity for both lengths.
            let zero_a = self.ctx.terms.mk_int(BigInt::from(0));
            axioms.push(self.ctx.terms.mk_ge(len_container, zero_a));
            let zero_b = self.ctx.terms.mk_int(BigInt::from(0));
            axioms.push(self.ctx.terms.mk_ge(len_contained, zero_b));

            // Constant folding for newly created str.len terms.
            // These weren't in the original formula so axiom 6 didn't catch them.
            for &(str_term, len_term) in &[(container, len_container), (contained, len_contained)] {
                if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(str_term) {
                    let char_count = s.chars().count();
                    let len_val = self.ctx.terms.mk_int(BigInt::from(char_count));
                    let const_eq = self.ctx.terms.mk_eq(len_term, len_val);
                    axioms.push(const_eq);
                }
            }

            // pred => str.len(container) >= str.len(contained)
            let ge = self.ctx.terms.mk_ge(len_container, len_contained);
            let implies = self.ctx.terms.mk_implies(pred_term, ge);
            axioms.push(implies);
        }

        // Axiom 9: Eager reduction lemmas for range-restricted integer functions.
        //
        // CVC5 term_registry.cpp:80-133 (eagerReduce): asserts range axioms at
        // term registration so the arithmetic solver inherently rejects out-of-range
        // assignments. Without these, the LIA solver treats str.to_int(x) etc. as
        // uninterpreted integers and can assign values like -2 or -5.
        //
        // str.to_int(x):    str.to_int(x) >= -1
        // str.to_code(x):   str.to_code(x) >= -1 AND str.to_code(x) <= 196607
        // str.indexof(x,y,n): str.indexof(x,y,n) >= -1 AND str.indexof(x,y,n) <= str.len(x)
        for (func_term, kind) in range_restricted_terms {
            let minus_one = self.ctx.terms.mk_int(BigInt::from(-1));
            axioms.push(self.ctx.terms.mk_ge(func_term, minus_one));

            if kind == 1 {
                // str.to_code upper bound: <= 196607 (Unicode max codepoint)
                let upper = self.ctx.terms.mk_int(BigInt::from(196_607));
                axioms.push(self.ctx.terms.mk_le(func_term, upper));

                // Conditional axioms for str.to_code(x) (#6353):
                //   len(x) = 1 => str.to_code(x) >= 0
                //   len(x) != 1 => str.to_code(x) = -1
                //
                // CVC5 reference: term_registry.cpp eagerReduce (lines 80-133).
                // These axioms link the string-integer boundary: the LIA solver
                // sees str.to_code(x) as uninterpreted and can assign values
                // like -1 even when len(x) = 1. The conditional axiom forces
                // the LIA solver to respect the str.to_code semantics.
                let x = match self.ctx.terms.get(func_term) {
                    TermData::App(_, args) if args.len() == 1 => Some(args[0]),
                    _ => None,
                };
                if let Some(x) = x {
                    let one = self.ctx.terms.mk_int(BigInt::from(1));
                    let len_x = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
                    let len_eq_1 = self.ctx.terms.mk_eq(len_x, one);
                    let zero = self.ctx.terms.mk_int(BigInt::from(0));

                    // len(x) = 1 => str.to_code(x) >= 0
                    let code_ge_0 = self.ctx.terms.mk_ge(func_term, zero);
                    let implies_ge = self.ctx.terms.mk_implies(len_eq_1, code_ge_0);
                    axioms.push(implies_ge);

                    // len(x) != 1 => str.to_code(x) = -1
                    let not_len_1 = self.ctx.terms.mk_not(len_eq_1);
                    let code_eq_m1 = self.ctx.terms.mk_eq(func_term, minus_one);
                    let implies_m1 = self.ctx.terms.mk_implies(not_len_1, code_eq_m1);
                    axioms.push(implies_m1);
                }
            } else if kind == 2 {
                // str.indexof upper bound: <= str.len(x)
                // CVC5 term_registry.cpp: indexof(x,y,n) <= len(x)
                debug_assert!(
                    matches!(self.ctx.terms.get(func_term), TermData::App(_, args) if args.len() == 3),
                    "BUG: str.indexof range axiom applied to term with arity != 3"
                );
                let x = match self.ctx.terms.get(func_term) {
                    TermData::App(_, args) => Some(args[0]),
                    _ => None,
                };
                if let Some(x) = x {
                    let len_x = self
                        .ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
                    axioms.push(self.ctx.terms.mk_le(func_term, len_x));
                }
            }
        }

        // Axiom 8: String equality implies corresponding length equality.
        //
        // (= s t) => (= (str.len s) (str.len t))
        // (= s "abc") => (= (str.len s) 3)
        //
        // This is essential for QF_SLIA integration: when string theory or the SAT
        // model sets an equality atom true, arithmetic constraints on str.len terms
        // must see the matching length fact.
        for (eq_term, lhs, rhs) in string_equalities {
            // Extract constant string lengths before mutable borrows
            let lhs_const_len = match self.ctx.terms.get(lhs) {
                TermData::Const(Constant::String(s)) => Some(s.chars().count()),
                _ => None,
            };
            let rhs_const_len = match self.ctx.terms.get(rhs) {
                TermData::Const(Constant::String(s)) => Some(s.chars().count()),
                _ => None,
            };

            let implied_len_eq = match (lhs_const_len, rhs_const_len) {
                (Some(lhs_len_val), _) => {
                    let rhs_len =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![rhs], Sort::Int);
                    let lhs_len_const = self.ctx.terms.mk_int(BigInt::from(lhs_len_val));
                    self.ctx.terms.mk_eq(rhs_len, lhs_len_const)
                }
                (_, Some(rhs_len_val)) => {
                    let lhs_len =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![lhs], Sort::Int);
                    let rhs_len_const = self.ctx.terms.mk_int(BigInt::from(rhs_len_val));
                    self.ctx.terms.mk_eq(lhs_len, rhs_len_const)
                }
                _ => {
                    let lhs_len =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![lhs], Sort::Int);
                    let rhs_len =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.len"), vec![rhs], Sort::Int);
                    self.ctx.terms.mk_eq(lhs_len, rhs_len)
                }
            };

            axioms.push(self.ctx.terms.mk_implies(eq_term, implied_len_eq));

            // Axiom 4b: Decompose any concat-length terms created by Axiom 8.
            //
            // Axiom 8 creates str.len(lhs) or str.len(rhs) for string equalities.
            // When lhs/rhs is a concat, this creates str.len(str.++(a,b,...)) that
            // the first-pass Axiom 4 never saw. Emit the decomposition now.
            //
            // Fix for concat-length axiom gap (#3526): without this, formulas like
            // (= (str.++ x y) "abc") with (= (str.len x) 2) (= (str.len y) 2)
            // are incorrectly SAT because len(x)+len(y)=4 != 3=len("abc") is never derived.
            let sides_to_check: Vec<TermId> = match (lhs_const_len, rhs_const_len) {
                (Some(_), _) => vec![rhs],
                (_, Some(_)) => vec![lhs],
                _ => vec![lhs, rhs],
            };
            for side in sides_to_check {
                if !seen_concat_len.contains(&side) {
                    if let TermData::App(Symbol::Named(n), cargs) = self.ctx.terms.get(side) {
                        if n == "str.++" && cargs.len() >= 2 {
                            seen_concat_len.insert(side);
                            let cargs: Vec<TermId> = cargs.clone();
                            let len_term = self.ctx.terms.mk_app(
                                Symbol::named("str.len"),
                                vec![side],
                                Sort::Int,
                            );
                            let len_parts: Vec<TermId> = cargs
                                .iter()
                                .map(|&arg| {
                                    self.ctx.terms.mk_app(
                                        Symbol::named("str.len"),
                                        vec![arg],
                                        Sort::Int,
                                    )
                                })
                                .collect();
                            // Non-negativity for each part
                            for (idx, &part) in len_parts.iter().enumerate() {
                                let arg = cargs[idx];
                                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                                axioms.push(self.ctx.terms.mk_ge(part, zero));

                                let zero_len = self.ctx.terms.mk_int(BigInt::from(0));
                                let len_eq_zero = self.ctx.terms.mk_eq(part, zero_len);
                                let empty = self.ctx.terms.mk_string(String::new());
                                let arg_eq_empty = self.ctx.terms.mk_eq(arg, empty);
                                axioms.push(self.ctx.terms.mk_implies(len_eq_zero, arg_eq_empty));

                                let empty_rev = self.ctx.terms.mk_string(String::new());
                                let arg_eq_empty_rev = self.ctx.terms.mk_eq(arg, empty_rev);
                                let zero_rev = self.ctx.terms.mk_int(BigInt::from(0));
                                let len_eq_zero_rev = self.ctx.terms.mk_eq(part, zero_rev);
                                axioms.push(
                                    self.ctx.terms.mk_implies(arg_eq_empty_rev, len_eq_zero_rev),
                                );

                                if let TermData::Const(Constant::String(s)) =
                                    self.ctx.terms.get(arg)
                                {
                                    let char_count =
                                        self.ctx.terms.mk_int(BigInt::from(s.chars().count()));
                                    axioms.push(self.ctx.terms.mk_eq(part, char_count));
                                }
                            }
                            let sum = self.ctx.terms.mk_add(len_parts);
                            let eq = self.ctx.terms.mk_eq(len_term, sum);
                            axioms.push(eq);
                        }
                    }
                }
            }
        }

        // (axiom set continues below; see collect_str_index_value_axioms for the
        // indexof-out-of-range and length-preserving-replace facts emitted on the
        // mixed string+array path.)

        // Axiom 10: Ground extended function equalities.
        // When an extf application has all-constant arguments, assert the ground
        // equality so the string solver can merge the extf EQC with the constant.
        // Without this, check_extf_reductions finds no constant in the EQC and
        // sets incomplete=true, causing the solver to return unknown.
        // Dedup: a term may appear via both str.len(extf) and standalone paths.
        let mut seen_extf: HashSet<TermId> = HashSet::default();
        for (extf_term, evaluated) in ground_extf_evals {
            if seen_extf.insert(extf_term) {
                let const_term = self.ctx.terms.mk_string(evaluated);
                let eq = self.ctx.terms.mk_eq(extf_term, const_term);
                axioms.push(eq);
            }
        }

        axioms
    }

    /// Collect VALUE axioms for `str.indexof` and `str.replace` whose result —
    /// or its length — is used as an array index in a mixed string+array problem.
    ///
    /// The combined array/EUF/LIA solver treats `str.indexof`/`str.replace`
    /// opaquely, so a string→Int op over them used as an array index never
    /// reaches the select congruence (#mix-str2int-array-index). Two SOUND facts
    /// (verified vs z3) close the common shapes:
    ///
    /// 1. `str.indexof` out of range:
    ///    `(=> (and (>= i 0) (> (+ i (str.len n)) (str.len s))) (= (str.indexof s n i) -1))`
    ///    The needle `n` cannot fit in `s` starting at `i` once `i + len(n) > len(s)`,
    ///    so there is no occurrence and the result is `-1`. Sound for ALL needles,
    ///    including the empty needle: the empty string matches at every position
    ///    `0..=len(s)` (so it is `i` when `i <= len(s)`), but the STRICT `>` bound
    ///    here fires only when `i > len(s)` for the empty needle, where the result
    ///    is indeed `-1` (no position `>= i` is `<= len(s)`).
    ///
    /// 2. length-preserving `str.replace`:
    ///    `(= (str.len (str.replace x p r)) (str.len x))` when `len(p) = len(r)`.
    ///    Replacing the first occurrence of `p` with an equal-length `r` (or no
    ///    occurrence, leaving `x` unchanged) preserves the length. Emitted only
    ///    when `p` and `r` are literals of equal length (a direct, sound check).
    pub(in crate::executor) fn collect_str_index_value_axioms(&mut self) -> Vec<TermId> {
        let roots = self.ctx.assertions.clone();
        // (indexof_term, s, n, i)
        let mut indexofs: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        // (replace_term, x) for length-preserving replaces.
        let mut len_preserving_replaces: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots;
        let mut visited: HashSet<TermId> = HashSet::default();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.indexof" && args.len() == 3 && seen.insert(term) {
                        indexofs.push((term, args[0], args[1], args[2]));
                    } else if name == "str.replace" && args.len() == 3 && seen.insert(term) {
                        let p_len = match self.ctx.terms.get(args[1]) {
                            TermData::Const(Constant::String(p)) => Some(p.chars().count()),
                            _ => None,
                        };
                        let r_len = match self.ctx.terms.get(args[2]) {
                            TermData::Const(Constant::String(r)) => Some(r.chars().count()),
                            _ => None,
                        };
                        if let (Some(pl), Some(rl)) = (p_len, r_len) {
                            if pl == rl {
                                len_preserving_replaces.push((term, args[0]));
                            }
                        }
                    }
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    let binding_vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                    let body_id = *body;
                    for val in binding_vals {
                        stack.push(val);
                    }
                    stack.push(body_id);
                }
                _ => {}
            }
        }

        // Map each string Var to its top-level-asserted concrete length, so the
        // source length of an `str.indexof` can be resolved to a constant. Only
        // GROUND-determined sources are used below — emitting a free conditional
        // (with an unconstrained `str.len(source)`) would let the solver pick the
        // length to force the `-1` branch and then stall a genuine-SAT instance to
        // Unknown (a completeness regression). Restricting to determined lengths
        // emits the unconditional `(= idx -1)` only when it is provably correct.
        let mut var_len: HashMap<TermId, usize> = HashMap::default();
        for &c in &self.ctx.assertions.clone() {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(c) {
                if name == "=" && args.len() == 2 {
                    let (l, r) = (args[0], args[1]);
                    let as_len_var = |t: TermId| -> Option<TermId> {
                        if let TermData::App(Symbol::Named(n), a) = self.ctx.terms.get(t) {
                            if n == "str.len" && a.len() == 1 {
                                return Some(a[0]);
                            }
                        }
                        None
                    };
                    let as_nat = |t: TermId| -> Option<usize> {
                        match self.ctx.terms.get(t) {
                            TermData::Const(Constant::Int(v)) if *v >= BigInt::from(0) => {
                                use num_traits::ToPrimitive;
                                v.to_usize()
                            }
                            _ => None,
                        }
                    };
                    if let (Some(v), Some(k)) = (as_len_var(l), as_nat(r)) {
                        var_len.insert(v, k);
                    } else if let (Some(v), Some(k)) = (as_len_var(r), as_nat(l)) {
                        var_len.insert(v, k);
                    }
                }
            }
        }
        // Resolve a string term's length to a concrete count when determined:
        // literal -> its length; a var with an asserted length; a concat of
        // determined parts -> their sum. None when not determined.
        fn resolve_len(
            exec: &Executor,
            var_len: &HashMap<TermId, usize>,
            t: TermId,
        ) -> Option<usize> {
            match exec.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => Some(s.chars().count()),
                TermData::Var(_, _) => var_len.get(&t).copied(),
                TermData::App(Symbol::Named(n), args) if n == "str.++" => {
                    let mut sum = 0usize;
                    for &a in args {
                        sum += resolve_len(exec, var_len, a)?;
                    }
                    Some(sum)
                }
                _ => None,
            }
        }

        let mut axioms = Vec::new();
        for (idx_term, s, n, i) in indexofs {
            // Require constant offset, constant needle length, and a determined
            // source length, so the out-of-range condition is decided NOW.
            let i_val = match self.ctx.terms.get(i) {
                TermData::Const(Constant::Int(v)) => Some(v.clone()),
                _ => None,
            };
            let n_len = match self.ctx.terms.get(n) {
                TermData::Const(Constant::String(ns)) => Some(ns.chars().count()),
                _ => None,
            };
            let s_len = resolve_len(self, &var_len, s);
            if let (Some(iv), Some(nl), Some(sl)) = (i_val, n_len, s_len) {
                // Out of range iff i >= 0 and i + len(needle) > len(s).
                if iv >= BigInt::from(0) && &iv + BigInt::from(nl) > BigInt::from(sl) {
                    let minus_one = self.ctx.terms.mk_int(BigInt::from(-1));
                    axioms.push(self.ctx.terms.mk_eq(idx_term, minus_one));
                }
            }
        }
        for (repl_term, x) in len_preserving_replaces {
            let len_repl =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![repl_term], Sort::Int);
            let len_x = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
            axioms.push(self.ctx.terms.mk_eq(len_repl, len_x));
        }
        axioms
    }
}
