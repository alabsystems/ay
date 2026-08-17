// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function reduction pre-registration for string theory.
//!
//! Emits CVC5-style reduction lemmas for `str.substr`, `str.replace`, and
//! `str.at` before the DPLL(T) solve loop.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::super::strings_eval::{ground_eval_int_term, ground_eval_string_term};

// Test-only override so unit tests can exercise the P2 path without mutating
// process-global environment state (the env read below is cached in a
// `OnceLock`, so `set_var` in one test would leak into every other test).
#[cfg(test)]
thread_local! {
    pub(in crate::executor) static STR_P2_TEST_OVERRIDE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Strings increment P2 master switch (default ON, `--dpll-no-str-p2` kill switch).
///
/// Gates the eager NON-GROUND extended-function reduction package
/// (Reynolds CAV'17 / CVC-style):
///   - `str.substr` reductions with SYMBOLIC start/length bounds (the
///     default path only preregisters syntactically-constant bounds, #4057);
///   - eager `str.indexof` first-occurrence reductions (the same axiom the
///     on-demand `StringLemmaKind::IndexofReduction` CEGAR path emits, but
///     available to the SAT/LIA core from iteration 0).
///
/// Default OFF keeps the solve pipeline byte-identical to pre-P2 behavior.
pub(in crate::executor) fn str_p2_enabled() -> bool {
    #[cfg(test)]
    if STR_P2_TEST_OVERRIDE.with(|c| c.get()) {
        return true;
    }
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: 7 conversions on its own target families plus the reduction
    // substrate P3/W4 build on; 0 disagreements, 0 regressions across the
    // solved-file sweeps, fuzz clean. Escalation passes only run AFTER the
    // default passes return Unknown. --dpll-no-str-p2 kills it.
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_str_p2)
}

impl Executor {
    /// Pre-register CVC5-style reduction lemmas for extended string functions.
    ///
    /// For `str.substr(s, n, m)`:
    ///   IF n >= 0 AND len(s) > n AND m > 0
    ///   THEN s = sk_pre ++ skt ++ sk_suf AND
    ///        len(sk_pre) = n AND
    ///        (len(sk_suf) = len(s) - (n+m) OR len(sk_suf) = 0) AND
    ///        len(skt) <= m
    ///   ELSE skt = ""
    ///   AND substr(s, n, m) = skt
    ///
    /// For `str.replace(x, y, z)`:
    ///   IF y = ""
    ///   THEN rpw = str.++(z, x)
    ///   ELIF contains(x, y)
    ///   THEN x = str.++(rp1, y, rp2) AND
    ///        rpw = str.++(rp1, z, rp2) AND
    ///        NOT contains(str.++(rp1, substr(y, 0, len(y)-1)), y)
    ///   ELSE rpw = x
    ///   AND replace(x, y, z) = rpw
    ///
    /// Reference: CVC5 `theory_strings_preprocess.cpp:62-121` (substr),
    ///            CVC5 `theory_strings_preprocess.cpp:572-631` (replace),
    ///            CVC5 `theory_strings_preprocess.cpp:527-571` (str.at)
    /// `p2_symbolic_only` (strings increment P2, enabled escalation
    /// pass): when true, the pass collects ONLY the P2 reduction classes —
    /// `str.substr` with NON-constant bounds and `str.indexof` — and ignores
    /// `enable_substr_and_at`/`enable_replace` (those classes are owned by
    /// the earlier effort passes, and re-emitting `str.at` reductions would
    /// mint fresh uncached skolems). When false, behavior is exactly the
    /// pre-P2 pipeline.
    pub(in crate::executor) fn preregister_extf_reductions(
        &mut self,
        assertions: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
        _decomposed_vars: &mut HashSet<TermId>,
        enable_substr_and_at: bool,
        enable_replace: bool,
        p2_symbolic_only: bool,
    ) -> (Vec<TermId>, Vec<TermId>) {
        let mut reductions = Vec::new();
        let mut reduced_term_ids = Vec::new();
        let _seen_reduced_terms: HashSet<TermId> = HashSet::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut input_contains_terms: HashSet<TermId> = HashSet::default();
        // Track haystack variables that receive a replace decomposition
        // (case 2: x = rp1 ++ y ++ rp2). These must be passed to the second
        // contains-decomposition pass to prevent double decomposition (#4057).
        let _replace_decomposed_haystacks: HashSet<TermId> = HashSet::default();

        // DFS scan for str.substr, str.replace, and str.at terms.
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited: HashSet<TermId> = HashSet::default();
        // Entries are `(substr_term, s, n, m)`.
        let mut substr_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        // Entries are `(replace_term, x, y, z)`.
        let mut replace_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        // Entries are `(at_term, s, n)`.
        let mut at_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        // Entries are `(replace_re[_all]_term, s, regex)`.
        let mut replace_re_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
        // Entries are `(indexof_term, s, w, n)`; this class is P2-only.
        let mut indexof_terms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
        // Effort flags are owned by the pre-P2 passes; the P2 escalation pass
        // collects exactly its own two classes.
        let enable_substr_and_at = enable_substr_and_at && !p2_symbolic_only;
        let enable_replace = enable_replace && !p2_symbolic_only;

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.contains" && args.len() == 2 {
                        input_contains_terms.insert(term);
                    }
                    if (enable_substr_and_at || p2_symbolic_only)
                        && name == "str.substr"
                        && args.len() == 3
                        && seen.insert(term)
                    {
                        // Skip fully-ground substr — Wave 0 handles those via
                        // ground_eval_string_term.
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        let constant_bounds = matches!(
                            self.ctx.terms.get(args[1]),
                            TermData::Const(Constant::Int(_))
                        ) && matches!(
                            self.ctx.terms.get(args[2]),
                            TermData::Const(Constant::Int(_))
                        );
                        // Soundness guard for #4057: eager non-ground substr
                        // reduction on symbolic lengths (for example
                        // str.substr(c, 0, str.len(e))) introduces branch-local
                        // skolems that can over-constrain circular formulas.
                        // Keep eager preregistration only for syntactically
                        // constant bounds; the theory-side extf evaluation can
                        // still reduce the deferred cases later once values
                        // become concrete.
                        //
                        // P2 (escalation pass only): lift the
                        // constant-bounds restriction. The reduction lemma
                        // itself never inspects the bound values — it is the
                        // SAME exact characterization of SMT-LIB `str.substr`
                        // for symbolic `n`/`m` (out-of-range/degenerate cases
                        // all land in the `skt = ""` else-branch), and the
                        // on-demand `SubstrReduction` CEGAR path already
                        // emits it verbatim for symbolic bounds. Running it
                        // only as an escalation AFTER the unchanged effort
                        // passes return Unknown means anything solvable
                        // today still solves identically first (the eager
                        // variant regressed Leetcode isNumber: the skolem web
                        // latched the strings core `incomplete` before the
                        // pure-LIA length contradiction could surface).
                        let want = if p2_symbolic_only {
                            !constant_bounds
                        } else {
                            constant_bounds
                        };
                        if !is_ground && want {
                            substr_terms.push((term, args[0], args[1], args[2]));
                        }
                    } else if enable_replace
                        && name == "str.replace"
                        && args.len() == 3
                        && seen.insert(term)
                    {
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            replace_terms.push((term, args[0], args[1], args[2]));
                        }
                    } else if enable_substr_and_at
                        && name == "str.at"
                        && args.len() == 2
                        && seen.insert(term)
                    {
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            at_terms.push((term, args[0], args[1]));
                        }
                    } else if p2_symbolic_only
                        && name == "str.indexof"
                        && args.len() == 3
                        && seen.insert(term)
                    {
                        // P2: eager first-occurrence reduction for non-ground
                        // `str.indexof`. Ground applications fold in Wave 0
                        // (`fold_ground_string_ops`) / evaluate via
                        // `ground_eval_int_term`, so they are skipped here.
                        let is_ground = ground_eval_int_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            indexof_terms.push((term, args[0], args[1], args[2]));
                        }
                    } else if enable_replace
                        && (name == "str.replace_re" || name == "str.replace_re_all")
                        && args.len() == 3
                        && ay_strings::regex_ground_evaluable(&self.ctx.terms, args[1])
                        && seen.insert(term)
                    {
                        // Partial regex-replace reduction (extf wave 2 Part B):
                        // only for GROUND engine-evaluable regexes; ground
                        // haystacks fold via Wave 0 evaluation instead.
                        let is_ground = ground_eval_string_term(&self.ctx.terms, term).is_some();
                        if !is_ground {
                            replace_re_terms.push((term, args[0], args[1]));
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

        // P2: emit eager `str.indexof` first-occurrence reductions.
        //
        // This is the SAME axiom the on-demand CEGAR path emits
        // (`StringLemmaKind::IndexofReduction`, strings_lemma/clauses.rs) —
        // preregistered so the SAT/LIA core sees the full constraint web from
        // iteration 0 instead of only after a theory stall. For
        // `t = (str.indexof s w n)` with search window
        // `win = substr(s, n, len(s) - n)` (window = `s` itself when `n` is
        // the literal 0, since `substr(s, 0, len(s)) = s`):
        //
        //   ite(n >= 0 and n <= len(s),
        //       ite(w = "",                                  [symbolic w only]
        //           t = n,
        //           ite(contains(win, w),
        //               and(win = io_pre ++ w ++ io_suf,
        //                   t = n + len(io_pre),
        //                   not(contains(io_pre ++ w[0..|w|-1], w))),
        //               t = -1)),
        //       t = -1)
        //
        // VALIDITY (each branch is exactly SMT-LIB `str.indexof` semantics,
        // so the reduction is a conservative extension — UNSAT stays sound;
        // SAT is re-checked by the definitive model-validation chokepoint):
        //   - `n < 0 ∨ n > len(s)`: no valid start position ⇒ t = -1.
        //   - `w = ""` with valid offset: the empty needle occurs at every
        //     position, the smallest `j >= n` is `n` ⇒ t = n.
        //   - occurrence case: in any real model choose `io_pre = win[0..r-n]`
        //     and `io_suf` the rest, where `r = indexof(s, w, n)`; then
        //     `t = n + len(io_pre) = r` and the leftmost guard holds — an
        //     occurrence of `w` inside `io_pre ++ w[0..|w|-1]` would start
        //     strictly before `r - n` in the window (any occurrence starting
        //     at p <= len(io_pre)-1 ends at p+|w| <= len(io_pre)+|w|-1, i.e.
        //     lies entirely inside that prefix string, and conversely), which
        //     would contradict `r` being the FIRST match at or after `n`.
        //   - no-occurrence case: t = -1 by definition.
        //
        // The io skolems reuse the `contains_pre`/`contains_post` cache keys
        // for `(win, w)`, so the eager contains-decomposition pass (which sees
        // `contains(win, w)` under the ITE condition with positive polarity)
        // produces the IDENTICAL decomposition equality instead of a second,
        // competing skolem pair.
        for &(t, s, w, n) in &indexof_terms {
            reduced_term_ids.push(t);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let const_w: Option<String> = match self.ctx.terms.get(w) {
                TermData::Const(Constant::String(cw)) => Some(cw.clone()),
                _ => None,
            };

            let t_eq_neg1 = self.ctx.terms.mk_eq(t, neg_one);
            let t_eq_n = self.ctx.terms.mk_eq(t, n);
            // Valid-offset guard: n >= 0 and n <= len(s). (`n = len(s)` is
            // in range: the empty needle still matches at the very end.)
            let c1 = self.ctx.terms.mk_ge(n, zero);
            let c2 = self.ctx.terms.mk_le(n, len_s);
            let cond_valid = self.ctx.terms.mk_and(vec![c1, c2]);

            // Global range fact, valid in every model: indexof >= -1.
            let t_ge_neg1 = self.ctx.terms.mk_ge(t, neg_one);

            // Empty CONSTANT needle: indexof(s, "", n) = n when the offset is
            // valid, -1 otherwise. No skolems or guards needed.
            if const_w.as_deref() == Some("") {
                let top = self.ctx.terms.mk_ite(cond_valid, t_eq_n, t_eq_neg1);
                reductions.push(top);
                reductions.push(t_ge_neg1);
                continue;
            }

            // Search window: `s` when n is the literal 0, else
            // substr(s, n, len(s) - n) — which is itself reduced by the
            // (P2 symbolic-bounds) substr loop below.
            let window = if matches!(
                self.ctx.terms.get(n),
                TermData::Const(Constant::Int(v)) if v == &BigInt::from(0)
            ) {
                s
            } else {
                let window_len = self.ctx.terms.mk_sub(vec![len_s, n]);
                let wterm = self.ctx.terms.mk_app(
                    Symbol::named("str.substr"),
                    vec![s, n, window_len],
                    Sort::String,
                );
                if seen.insert(wterm) {
                    substr_terms.push((wterm, s, n, window_len));
                }
                wterm
            };

            let io_pre = skolem_cache.contains_pre(&mut self.ctx.terms, window, w);
            let io_suf = skolem_cache.contains_post(&mut self.ctx.terms, window, w);

            // Found branch: window = io_pre ++ w ++ io_suf, t = n + len(io_pre).
            let concat = self.ctx.terms.mk_app(
                Symbol::named("str.++"),
                vec![io_pre, w, io_suf],
                Sort::String,
            );
            let window_eq = self.ctx.terms.mk_eq(window, concat);
            let len_io_pre =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![io_pre], Sort::Int);
            let n_plus_pre = self.ctx.terms.mk_add(vec![n, len_io_pre]);
            let t_eq_pos = self.ctx.terms.mk_eq(t, n_plus_pre);

            // Leftmost guard haystack: io_pre ++ w[0..|w|-1] (folded when the
            // needle is a literal; single-char needles collapse to io_pre).
            let leftmost_hay = if let Some(cw) = const_w.as_deref() {
                let mut chars: Vec<char> = cw.chars().collect();
                chars.pop();
                if chars.is_empty() {
                    io_pre
                } else {
                    let pre_w_const: String = chars.into_iter().collect();
                    let pre_w = self.ctx.terms.mk_string(pre_w_const);
                    self.ctx.terms.mk_app(
                        Symbol::named("str.++"),
                        vec![io_pre, pre_w],
                        Sort::String,
                    )
                }
            } else {
                let len_w = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![w], Sort::Int);
                let one = self.ctx.terms.mk_int(BigInt::from(1));
                let len_w_minus_1 = self.ctx.terms.mk_sub(vec![len_w, one]);
                let zero_sub = self.ctx.terms.mk_int(BigInt::from(0));
                let ypre = self.ctx.terms.mk_app(
                    Symbol::named("str.substr"),
                    vec![w, zero_sub, len_w_minus_1],
                    Sort::String,
                );
                // Reduce the internal w[0..|w|-1] substr too (symbolic
                // bounds — P2 lifts the constant-bounds restriction).
                if seen.insert(ypre) {
                    substr_terms.push((ypre, w, zero_sub, len_w_minus_1));
                }
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![io_pre, ypre], Sort::String)
            };
            let leftmost_ctn = self.ctx.terms.mk_app(
                Symbol::named("str.contains"),
                vec![leftmost_hay, w],
                Sort::Bool,
            );
            let contains_atom =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.contains"), vec![window, w], Sort::Bool);
            // Guard atoms are internal to the reduction: mark them reduced so
            // the extf predicate pass does not treat them as unresolved
            // user-level predicates and re-latch `incomplete` (same rationale
            // as the dynamic IndexofReduction path). Their semantics stay
            // enforced by the emitted axioms + the model-validation chokepoint.
            reduced_term_ids.push(contains_atom);
            reduced_term_ids.push(leftmost_ctn);

            let not_leftmost = self.ctx.terms.mk_not(leftmost_ctn);
            let found_branch = self
                .ctx
                .terms
                .mk_and(vec![window_eq, t_eq_pos, not_leftmost]);
            let inner2 = self
                .ctx
                .terms
                .mk_ite(contains_atom, found_branch, t_eq_neg1);

            // Symbolic needle: peel the w = "" case (result is the offset).
            let inner1 = if const_w.is_some() {
                inner2
            } else {
                let empty = self.ctx.terms.mk_string(String::new());
                let w_empty = self.ctx.terms.mk_eq(w, empty);
                self.ctx.terms.mk_ite(w_empty, t_eq_n, inner2)
            };
            let top = self.ctx.terms.mk_ite(cond_valid, inner1, t_eq_neg1);
            reductions.push(top);
            reductions.push(t_ge_neg1);

            // LIA coupling facts (each VALID for real indexof, so they only
            // prune — never exclude a real model):
            //   t = -1 ∨ t >= n        (a found position is at or after n)
            //   t = -1 ∨ t + |w| <= |s| (a found occurrence fits inside s;
            //                            for w = "" this is t <= len(s) — true
            //                            since then t = n <= len(s))
            let t_ge_n = self.ctx.terms.mk_ge(t, n);
            reductions.push(self.ctx.terms.mk_or(vec![t_eq_neg1, t_ge_n]));
            let len_w_term = if let Some(cw) = const_w.as_deref() {
                self.ctx.terms.mk_int(BigInt::from(cw.chars().count()))
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![w], Sort::Int)
            };
            let t_plus_w = self.ctx.terms.mk_add(vec![t, len_w_term]);
            let fits = self.ctx.terms.mk_le(t_plus_w, len_s);
            reductions.push(self.ctx.terms.mk_or(vec![t_eq_neg1, fits]));

            // Non-negativity + lengthPositive bridges for the io skolems
            // (same pattern as the substr/replace loops below).
            for &sk in &[io_pre, io_suf] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Emit substr reduction lemmas.
        for (substr_term, s, n, m) in substr_terms {
            reduced_term_ids.push(substr_term);
            // Reuse canonical skolems per substr term.
            let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, substr_term);
            let skt = skolem_cache.substr_result(&mut self.ctx.terms, substr_term);
            let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, substr_term);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));

            // len(s)
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

            // Condition: n >= 0 AND len(s) > n AND m > 0
            let c1 = self.ctx.terms.mk_ge(n, zero);
            let c2 = self.ctx.terms.mk_gt(len_s, n);
            let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
            let c3 = self.ctx.terms.mk_gt(m, zero2);
            let cond = self.ctx.terms.mk_and(vec![c1, c2, c3]);

            // THEN branch:
            // b1: s = sk_pre ++ skt ++ sk_suf
            let concat = self.ctx.terms.mk_app(
                Symbol::named("str.++"),
                vec![sk_pre, skt, sk_suf],
                Sort::String,
            );
            // Internal concat introduced by eager substr reduction. Mark as
            // reduced so the string NF checker does not treat it as a primary
            // concat source and derive branch-local conflicts (#4057).
            reduced_term_ids.push(concat);
            let b11 = self.ctx.terms.mk_eq(s, concat);

            // NOTE: We do NOT mark the substr haystack in decomposed_vars here.
            // The global ExecutorSkolemCache ensures canonical skolems, so the
            // second-pass contains decomposition (from replace reductions) can
            // safely decompose this variable without creating competing equations.
            // Previously this blocked the #4057 fix path.

            // b2: len(sk_pre) = n
            let len_sk_pre =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk_pre], Sort::Int);
            let b12 = self.ctx.terms.mk_eq(len_sk_pre, n);

            // b3: len(sk_suf) = len(s) - (n+m) OR len(sk_suf) = 0
            let len_sk_suf =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk_suf], Sort::Int);
            let n_plus_m = self.ctx.terms.mk_add(vec![n, m]);
            let len_s2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let remainder = self.ctx.terms.mk_sub(vec![len_s2, n_plus_m]);
            let suf_eq_remainder = self.ctx.terms.mk_eq(len_sk_suf, remainder);
            let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
            let suf_eq_zero = self.ctx.terms.mk_eq(len_sk_suf, zero3);
            let b13 = self.ctx.terms.mk_or(vec![suf_eq_remainder, suf_eq_zero]);

            // b4: len(skt) <= m
            let len_skt = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
            let b14 = self.ctx.terms.mk_le(len_skt, m);

            let then_branch = self.ctx.terms.mk_and(vec![b11, b12, b13, b14]);

            // ELSE branch: skt = ""
            let empty = self.ctx.terms.mk_string(String::new());
            let else_branch = self.ctx.terms.mk_eq(skt, empty);

            // ITE(cond, then, else)
            let ite = self.ctx.terms.mk_ite(cond, then_branch, else_branch);
            reductions.push(ite);

            // Bridge: substr(s, n, m) = skt
            let bridge = self.ctx.terms.mk_eq(substr_term, skt);
            reductions.push(bridge);

            // Non-negativity for all skolem lengths.
            for &sk in &[sk_pre, skt, sk_suf] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));
            }

            // lengthPositive bridge for all skolems.
            for &sk in &[sk_pre, skt, sk_suf] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Emit replace reduction lemmas.
        for (replace_term, x, y, z) in replace_terms {
            reduced_term_ids.push(replace_term);
            // Reuse canonical skolems per replace term.
            let rpw = skolem_cache.replace_result(&mut self.ctx.terms, replace_term);
            let rp1 = skolem_cache.replace_pre(&mut self.ctx.terms, replace_term);
            let rp2 = skolem_cache.replace_suffix(&mut self.ctx.terms, replace_term);

            let empty = self.ctx.terms.mk_string(String::new());

            // Case 1: y = "" => rpw = str.++(z, x)
            let y_eq_empty = self.ctx.terms.mk_eq(y, empty);
            let concat_zx =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![z, x], Sort::String);
            // Internal concat introduced by eager replace reduction. Mark as
            // reduced to keep NF checks focused on user-level concat terms.
            reduced_term_ids.push(concat_zx);
            let rpw_eq_zx = self.ctx.terms.mk_eq(rpw, concat_zx);

            // Case 2: y != "" AND contains(x, y) =>
            //   x = rp1 ++ y ++ rp2 AND rpw = rp1 ++ z ++ rp2 AND
            //   NOT contains(rp1 ++ substr(y, 0, len(y)-1), y)
            let contains_xy =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);
            // `contains(x, y)` introduced by replace reduction is an internal
            // branch guard. If this atom was not present in the original
            // assertions, mark it reduced so core predicate evaluation does
            // not treat it as a user-level fact and generate spurious
            // conflicts from branch-local values (#4057).
            if !input_contains_terms.contains(&contains_xy) {
                reduced_term_ids.push(contains_xy);
            }
            let concat_decomp =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, y, rp2], Sort::String);
            reduced_term_ids.push(concat_decomp);
            let x_eq_decomp = self.ctx.terms.mk_eq(x, concat_decomp);

            // NOTE: We do NOT mark the replace haystack in decomposed_vars here.
            // The global ExecutorSkolemCache ensures canonical skolems, so the
            // second-pass contains decomposition can safely process contains(x, y)
            // from replace reductions without creating competing equations.

            let concat_result =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, z, rp2], Sort::String);
            reduced_term_ids.push(concat_result);
            let rpw_eq_result = self.ctx.terms.mk_eq(rpw, concat_result);

            // First-occurrence guard: NOT contains(rp1 ++ substr(y, 0, len(y)-1), y)
            let len_y = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let len_y_minus_1 = self.ctx.terms.mk_sub(vec![len_y, one]);
            let zero_rep = self.ctx.terms.mk_int(BigInt::from(0));
            let y_prefix = self.ctx.terms.mk_app(
                Symbol::named("str.substr"),
                vec![y, zero_rep, len_y_minus_1],
                Sort::String,
            );
            // Internal helper substr used only in the replace "first
            // occurrence" guard.
            reduced_term_ids.push(y_prefix);
            let rp1_y_prefix =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![rp1, y_prefix], Sort::String);
            reduced_term_ids.push(rp1_y_prefix);
            let contains_guard = self.ctx.terms.mk_app(
                Symbol::named("str.contains"),
                vec![rp1_y_prefix, y],
                Sort::Bool,
            );
            if !input_contains_terms.contains(&contains_guard) {
                reduced_term_ids.push(contains_guard);
            }
            let not_contains = self.ctx.terms.mk_not(contains_guard);
            let case2_body = self
                .ctx
                .terms
                .mk_and(vec![x_eq_decomp, rpw_eq_result, not_contains]);

            // Case 3: y != "" AND NOT contains(x, y) => rpw = x
            let rpw_eq_x = self.ctx.terms.mk_eq(rpw, x);

            // Build the three-way ITE:
            // IF y = "" THEN rpw = z ++ x
            // ELIF contains(x, y) THEN <case2_body>
            // ELSE rpw = x
            let inner_ite = self.ctx.terms.mk_ite(contains_xy, case2_body, rpw_eq_x);
            let outer_ite = self.ctx.terms.mk_ite(y_eq_empty, rpw_eq_zx, inner_ite);
            reductions.push(outer_ite);

            // Bridge: replace(x, y, z) = rpw
            let bridge = self.ctx.terms.mk_eq(replace_term, rpw);
            reductions.push(bridge);

            // Non-negativity + lengthPositive for skolems.
            for &sk in &[rpw, rp1, rp2] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));

                let len_sk2 = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk2, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Emit str.at reduction lemmas.
        // CVC5 reference: theory_strings_preprocess.cpp:527-571
        //
        // str.at(s, n) = skt where:
        //   IF n >= 0 AND n < len(s)
        //   THEN s = sk1 ++ unit(skt) ++ sk2 AND
        //        len(sk1) = n AND
        //        len(sk2) = len(s) - (n+1)
        //
        // skt is a unit-length string (or empty if out of bounds).
        for (at_term, s, n) in at_terms {
            reduced_term_ids.push(at_term);

            let skt = self.ctx.terms.mk_fresh_var("sk_at_res", Sort::String);
            let sk1 = self.ctx.terms.mk_fresh_var("sk_at_pre", Sort::String);
            let sk2 = self.ctx.terms.mk_fresh_var("sk_at_suf", Sort::String);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let one = self.ctx.terms.mk_int(BigInt::from(1));

            // Condition: n >= 0 AND n < len(s)
            let c1 = self.ctx.terms.mk_ge(n, zero);
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let c2 = self.ctx.terms.mk_gt(len_s, n);
            let cond = self.ctx.terms.mk_and(vec![c1, c2]);

            // THEN branch:
            // s = sk1 ++ skt ++ sk2
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![sk1, skt, sk2], Sort::String);
            // Internal concat from eager str.at reduction. Mark as reduced so
            // the strings NF checker does not treat it as a primary concat
            // source and derive spurious conflicts (#4080).
            reduced_term_ids.push(concat);
            let b1 = self.ctx.terms.mk_eq(s, concat);

            // len(sk1) = n
            let len_sk1 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![sk1], Sort::Int);
            let b2 = self.ctx.terms.mk_eq(len_sk1, n);

            // len(sk2) = len(s) - (n+1)
            let len_sk2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![sk2], Sort::Int);
            let n_plus_1 = self.ctx.terms.mk_add(vec![n, one]);
            let len_s2 = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let remainder = self.ctx.terms.mk_sub(vec![len_s2, n_plus_1]);
            let b3 = self.ctx.terms.mk_eq(len_sk2, remainder);

            // len(skt) = 1 (unit length when in bounds)
            let len_skt = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
            let b4 = self.ctx.terms.mk_eq(len_skt, one);

            let then_branch = self.ctx.terms.mk_and(vec![b1, b2, b3, b4]);

            // cond => then_branch (implication, not ITE)
            // When out of bounds, skt is unconstrained per SMT-LIB semantics.
            let lemma = self.ctx.terms.mk_implies(cond, then_branch);
            reductions.push(lemma);

            // Bridge: str.at(s, n) = skt
            let bridge = self.ctx.terms.mk_eq(at_term, skt);
            reductions.push(bridge);

            // Non-negativity + lengthPositive for string skolems.
            for &sk in &[skt, sk1, sk2] {
                let len_sk = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_sk = self.ctx.terms.mk_int(BigInt::from(0));
                reductions.push(self.ctx.terms.mk_ge(len_sk, zero_sk));

                let len_sk2_lp =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![sk], Sort::Int);
                let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
                let len_eq_zero = self.ctx.terms.mk_eq(len_sk2_lp, zero_lp);
                let empty_lp = self.ctx.terms.mk_string(String::new());
                let sk_eq_empty = self.ctx.terms.mk_eq(sk, empty_lp);
                reductions.push(self.ctx.terms.mk_implies(len_eq_zero, sk_eq_empty));
                reductions.push(self.ctx.terms.mk_implies(sk_eq_empty, len_eq_zero));
            }
        }

        // Partial regex-replace reductions (extf wave 2 Part B), GROUND
        // engine-evaluable regexes only:
        //
        //   (str.in_re s (re.++ re.all R re.all)) ∨ (r = s)
        //
        // "No match anywhere in s → result is s unchanged" — valid for both
        // str.replace_re (first match) and str.replace_re_all (all matches).
        // Marking the application reduced stops the extf passes latching
        // incomplete; exact match semantics are enforced by ground
        // evaluation once `s` resolves (leftmost-shortest; replace_re_all
        // replaces only NON-EMPTY matches) plus the definitive
        // model-validation chokepoint. An unresolved membership latches the
        // regexp solver's incompleteness, keeping Unknown honest.
        for (rre_term, s, re) in replace_re_terms {
            reduced_term_ids.push(rre_term);
            let re_all_l = self
                .ctx
                .terms
                .mk_app(Symbol::named("re.all"), vec![], Sort::RegLan);
            let re_all_r = self
                .ctx
                .terms
                .mk_app(Symbol::named("re.all"), vec![], Sort::RegLan);
            let window = self.ctx.terms.mk_app(
                Symbol::named("re.++"),
                vec![re_all_l, re, re_all_r],
                Sort::RegLan,
            );
            let match_atom =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.in_re"), vec![s, window], Sort::Bool);
            let r_eq_s = self.ctx.terms.mk_eq(rre_term, s);
            reductions.push(self.ctx.terms.mk_or(vec![match_atom, r_eq_s]));

            // Result skolem bridge (mirrors the substr/at reductions): give
            // the application's EQC a plain string VARIABLE so the normal
            // form machinery does not bail (Incomplete) on an opaque extf
            // application component.
            let rsk = skolem_cache.replace_result(&mut self.ctx.terms, rre_term);
            let bridge = self.ctx.terms.mk_eq(rre_term, rsk);
            reductions.push(bridge);
            let len_rsk = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![rsk], Sort::Int);
            let zero_rsk = self.ctx.terms.mk_int(BigInt::from(0));
            reductions.push(self.ctx.terms.mk_ge(len_rsk, zero_rsk));
            let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
            let len_eq_zero = self.ctx.terms.mk_eq(len_rsk, zero_lp);
            let empty_lp = self.ctx.terms.mk_string(String::new());
            let rsk_eq_empty = self.ctx.terms.mk_eq(rsk, empty_lp);
            reductions.push(self.ctx.terms.mk_implies(len_eq_zero, rsk_eq_empty));
            reductions.push(self.ctx.terms.mk_implies(rsk_eq_empty, len_eq_zero));
        }

        (reductions, reduced_term_ids)
    }
}
