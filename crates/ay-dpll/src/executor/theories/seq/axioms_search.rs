// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Search-family seq axiom generation: contains, extract, prefixof, suffixof.
//!
//! Index-finding and replacement operations (indexof, last_indexof, replace)
//! are in the sibling `axioms_indexof` module.

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use ay_core::kani_compat::DetHashMap as HashMap;

use super::super::super::Executor;
use super::ground::SeqTri;
use super::scan::SeqTermScan;
use ay_core::term::{Constant, Symbol, TermData, TermId};

/// Which end of the haystack a pairwise compatibility check aligns from.
///
/// `prefixof` needles align at index 0 (the head); `suffixof` needles align at
/// the tail. Two needles asserted over the SAME haystack must be comparable from
/// that shared end.
#[derive(Clone, Copy)]
enum CompatEnd {
    Prefix,
    Suffix,
}

impl Executor {
    /// Generate `seq.contains` axioms (#5841, #6024).
    ///
    /// For each `seq.contains(s, t)` term `c`:
    /// - Ground: when s and t resolve to concrete sequences, force c = true/false
    /// - Positive: `c => s = sk_left ++ t ++ sk_right`  (Z3: theory_seq.cpp:3104)
    /// - Positive: `c => len(sk_left) >= 0 AND len(sk_right) >= 0`
    /// - Length: `c => len(s) >= len(t)`
    ///
    /// The ground evaluation (#6024) prevents false-SAT on concrete sequences by
    /// directly evaluating containment when both s and t are ground (composed of
    /// seq.unit/seq.++/seq.empty over constants). This mirrors Z3's `canonizes`
    /// mechanism. For symbolic sequences, !contains incompleteness remains (no
    /// axiom can force contains = true without concrete evaluation).
    pub(super) fn generate_seq_contains_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());

        // Build ground-sequence map from equality assertions for concrete evaluation (#6024).
        let ground_map = self.build_ground_seq_map();

        for &(contains_term, s, t) in &scan.contains_terms {
            let seq_sort = self.ctx.terms.sort(s).clone();

            // Self-subsequence containment (#seq-contains-self-extract): a
            // sequence ALWAYS contains any `seq.extract` window of ITSELF — even
            // an out-of-bounds / empty window, since the empty sequence is a
            // subsequence of everything. So `contains(s, (seq.extract s i n))`,
            // and in particular `contains(s, (seq.at s i))` (which desugars to
            // `contains(s, (seq.extract s i 1))`), is UNCONDITIONALLY true, and
            // its negation was wrongly SAT. Force it true when the needle is an
            // extract of the SAME base `s` (a DIFFERENT base is not
            // unconditionally contained). Sound per SMT-LIB — z3 proves the
            // negation unsat for all i, n.
            let t_is_self_extract = matches!(
                self.ctx.terms.get(t),
                TermData::App(Symbol::Named(en), eargs)
                    if en == "seq.extract" && eargs.len() == 3 && eargs[0] == s
            );
            if t_is_self_extract {
                axioms.push(contains_term);
            }

            // === Ground evaluation (#6024): if both s and t resolve to concrete ===
            // sequences (via equality assertions), evaluate contains directly.
            // This prevents false-SAT when asserting !contains on concrete sequences.
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                if self.ground_seq_contains(&s_elems, &t_elems) {
                    axioms.push(contains_term); // Force contains = true
                } else {
                    let not_c = self.ctx.terms.mk_not(contains_term);
                    axioms.push(not_c); // Force contains = false
                }
                // Skip the redundant Skolem decomposition ONLY when both
                // operands are DIRECTLY ground literals (`seq.unit`/`seq.++`/
                // `seq.empty` over constants — e.g. after determined-var
                // inlining). The forced boolean is then authoritative, and over
                // a multi-element CONCAT container the `contains(s,t) =>
                // s = sk_left ++ t ++ sk_right` axiom only injects two
                // unconstrained fresh Skolem seq vars the combined seq theory
                // cannot reconcile, fail-closing an otherwise-SAT model to
                // Unknown (#seq-redundant-skolem).
                //
                // When the haystack is an nth-RECONSTRUCTED variable (resolved
                // only through the ground_map, NOT directly ground), the
                // variable still needs the structural decomposition to build a
                // full in-loop model, so KEEP the Skolem there (#6028).
                if self.try_extract_ground_seq(s).is_some()
                    && self.try_extract_ground_seq(t).is_some()
                {
                    continue;
                }
            }

            // Skolem witnesses: sk_left, sk_right such that
            // contains(s, t) => s = sk_left ++ t ++ sk_right
            let sk_left = self.ctx.terms.mk_fresh_var("seq.cnt.l", seq_sort.clone());
            let sk_right = self.ctx.terms.mk_fresh_var("seq.cnt.r", seq_sort.clone());

            // s = sk_left ++ t ++ sk_right
            let inner_concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![t, sk_right], seq_sort.clone());
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_left, inner_concat],
                seq_sort,
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);

            // contains(s, t) => decomposition
            axioms.push(self.ctx.terms.mk_implies(contains_term, decomp));

            // contains(s, t) => len(sk_left) >= 0
            let len_left = self.mk_seq_len(sk_left);
            let ge_left = self.ctx.terms.mk_ge(len_left, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_left));

            // contains(s, t) => len(sk_right) >= 0
            let len_right = self.mk_seq_len(sk_right);
            let ge_right = self.ctx.terms.mk_ge(len_right, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_right));

            // contains(s, t) => len(s) >= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let ge_len = self.ctx.terms.mk_ge(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_len));
        }

        axioms
    }

    /// Generate `seq.contains` TRANSITIVITY axioms (#seq-contains-transitivity).
    ///
    /// Subsequence containment is transitive: `contains(x, y) ∧ contains(y, z)
    /// ⟹ contains(x, z)`. The per-atom skolem decomposition in
    /// [`generate_seq_contains_axioms`](Self::generate_seq_contains_axioms)
    /// exposes each `contains` as an INDEPENDENT placement witness, so the
    /// EUF/length core never chains two of them and
    /// `contains(a,b) ∧ contains(b,c) ∧ ¬contains(a,c)` was wrongly SAT (AY even
    /// printed a model violating its own third assertion).
    ///
    /// For every ordered pair of `contains` atoms sharing a middle operand —
    /// `contains(x, y)` and `contains(y, z)` — emit the transitivity implication,
    /// materializing the (hash-consed) conclusion `contains(x, z)`. A bounded
    /// fixpoint over the finite set of scanned sequence terms takes the
    /// transitive CLOSURE, so longer chains (`a ⊇ b ⊇ c ⊇ d`) are closed too; the
    /// per-pair `present` dedup caps the number of derived atoms at one per
    /// ordered term pair. Sound: every implication is a semantic consequence of
    /// containment transitivity (z3 proves the three-atom negation unsat), so it
    /// can only REMOVE spurious models, never a genuine one.
    pub(super) fn generate_seq_contains_transitivity_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut axioms = Vec::new();
        // (contains_term, haystack, needle) edges; seeded from the scan, grown to
        // the transitive closure below.
        let mut edges: Vec<(TermId, TermId, TermId)> = scan
            .contains_terms
            .iter()
            .map(|&(term, s, t)| (term, s, t))
            .collect();
        let mut present: HashSet<(TermId, TermId)> =
            edges.iter().map(|&(_, s, t)| (s, t)).collect();
        // Bounded fixpoint: process edges by index; newly derived edges are
        // appended and processed in turn. Terminates because `present` admits at
        // most one edge per (haystack, needle) pair over the finite term set.
        let mut idx = 0;
        while idx < edges.len() {
            let (xy_term, x, y) = edges[idx];
            idx += 1;
            // Snapshot the `(y, z)` successor edges to avoid borrowing `edges`
            // while we push to it.
            let successors: Vec<(TermId, TermId)> = edges
                .iter()
                .filter(|&&(_, s2, _)| s2 == y)
                .map(|&(term2, _, z)| (term2, z))
                .collect();
            for (yz_term, z) in successors {
                // `contains(x, x)` is reflexively true — no information; and the
                // conclusion must be well-typed (same sequence sort).
                if x == z || self.ctx.terms.sort(x) != self.ctx.terms.sort(z) {
                    continue;
                }
                let xz_term = self.ctx.terms.mk_app(
                    Symbol::named("seq.contains"),
                    vec![x, z],
                    ay_core::Sort::Bool,
                );
                let premise = self.ctx.terms.mk_and(vec![xy_term, yz_term]);
                axioms.push(self.ctx.terms.mk_implies(premise, xz_term));
                if present.insert((x, z)) {
                    edges.push((xz_term, x, z));
                }
            }
        }
        axioms
    }

    /// Generate `seq.extract` axioms (#5841).
    ///
    /// For each `seq.extract(s, i, n)` term `e`:
    /// - `0 <= i AND i <= len(s) AND n >= 0 => s = sk_pre ++ e ++ sk_post`
    /// - `0 <= i AND i <= len(s) => len(sk_pre) = i`
    /// - `0 <= i AND i <= len(s) AND n >= 0 AND len(s) >= n + i => len(e) = n`
    /// - `0 <= i AND i <= len(s) AND n >= 0 AND len(s) < n + i => len(e) = len(s) - i`
    /// - `i < 0 OR i >= len(s) OR n <= 0 => e = seq.empty`
    ///
    /// Reference: Z3 seq_axioms.cpp:196-263
    pub(super) fn generate_seq_extract_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();
        // Var->const map so a symbolic index/length pinned to a literal (e.g.
        // `(seq.at s n0)` with `(= n0 1)`, which elaborates to
        // `(seq.extract s n0 1)`) still hits ground evaluation below. Resolving
        // i/n to their pinned constants and asserting the structural axiom on
        // the ORIGINAL `extract_term` is a sound congruence consequence of the
        // user's `(= n0 1)` equality (#seq-at-index-alias).
        let int_const_aliases = self.build_int_const_alias_map();

        for &(extract_term, s, i, n) in &scan.extract_terms {
            // Ground evaluation (#6040): when s is ground and i, n are constants,
            // compute the extraction result directly and force it.
            let i = self.resolve_int_const(i, &int_const_aliases);
            let n = self.resolve_int_const(n, &int_const_aliases);
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            if let Some(s_elems) = self.try_extract_ground_seq(s_ground) {
                if let (
                    TermData::Const(Constant::Int(i_val)),
                    TermData::Const(Constant::Int(n_val)),
                ) = (self.ctx.terms.get(i), self.ctx.terms.get(n))
                {
                    if let (Some(i_usize), Some(n_usize)) = (i_val.to_usize(), n_val.to_usize()) {
                        let seq_sort = self.ctx.terms.sort(s).clone();
                        let result_elems: Vec<TermId> = if i_usize < s_elems.len() && n_usize > 0 {
                            let end = (i_usize + n_usize).min(s_elems.len());
                            s_elems[i_usize..end].to_vec()
                        } else {
                            vec![] // out of bounds or n=0 → empty
                        };
                        // Force ground result via len + nth element equalities.
                        // Structural synthesis (seq.++ chains) doesn't work because
                        // the EUF solver lacks injectivity for seq.++. Instead, emit:
                        //   len(extract_term) = |result|
                        //   nth(extract_term, 0) = c0, nth(extract_term, 1) = c1, ...
                        // This lets the solver derive contradictions element-wise.
                        if result_elems.is_empty() {
                            let empty = self.mk_seq_empty(&seq_sort);
                            axioms.push(self.ctx.terms.mk_eq(extract_term, empty));
                            // Force len = 0 so arithmetic on len(extract) resolves.
                            let len_e = self.mk_seq_len(extract_term);
                            axioms.push(self.ctx.terms.mk_eq(len_e, zero));
                        } else if result_elems.len() == 1 {
                            // Single element: seq.unit is injective, so direct
                            // equality works: extract_term = seq.unit(c).
                            axioms.push(self.ctx.terms.mk_eq(extract_term, result_elems[0]));
                        } else {
                            // Multi-element: len + nth + concat nth materialization (#6040).
                            let elem_sort = seq_sort
                                .seq_element()
                                .cloned()
                                .unwrap_or(ay_core::Sort::Int);
                            let n_elems = result_elems.len();
                            let len_e = self.mk_seq_len(extract_term);
                            let n_int = self.ctx.terms.mk_int(BigInt::from(n_elems));
                            axioms.push(self.ctx.terms.mk_eq(len_e, n_int));
                            for (k, elem) in result_elems.iter().enumerate() {
                                let inner_c = match self.ctx.terms.get(*elem) {
                                    TermData::App(Symbol::Named(name), args)
                                        if name == "seq.unit" && args.len() == 1 =>
                                    {
                                        args[0]
                                    }
                                    _ => continue,
                                };
                                let idx = self.ctx.terms.mk_int(BigInt::from(k));
                                let nth_e = self.ctx.terms.mk_app(
                                    Symbol::named("seq.nth"),
                                    vec![extract_term, idx],
                                    elem_sort.clone(),
                                );
                                axioms.push(self.ctx.terms.mk_eq(nth_e, inner_c));
                            }
                            for &(concat_term, _) in &scan.concat_terms {
                                if self.ctx.terms.sort(concat_term) != &seq_sort {
                                    continue;
                                }
                                let eq_cond = self.ctx.terms.mk_eq(extract_term, concat_term);
                                for k in 0..n_elems {
                                    let idx = self.ctx.terms.mk_int(BigInt::from(k));
                                    let nth_e = self.ctx.terms.mk_app(
                                        Symbol::named("seq.nth"),
                                        vec![extract_term, idx],
                                        elem_sort.clone(),
                                    );
                                    let nth_c = self.ctx.terms.mk_app(
                                        Symbol::named("seq.nth"),
                                        vec![concat_term, idx],
                                        elem_sort.clone(),
                                    );
                                    let nth_eq = self.ctx.terms.mk_eq(nth_e, nth_c);
                                    axioms.push(self.ctx.terms.mk_implies(eq_cond, nth_eq));
                                }
                            }
                        }
                        // Ground evaluation complete; skip skolem decomposition.
                        continue;
                    }
                }
            }
            let seq_sort = self.ctx.terms.sort(s).clone();
            let len_s = self.mk_seq_len(s);
            let len_e = self.mk_seq_len(extract_term);

            // Skolems: sk_pre (prefix of length i), sk_post (suffix after extract)
            let sk_pre = self.ctx.terms.mk_fresh_var("seq.pre", seq_sort.clone());
            let sk_post = self.ctx.terms.mk_fresh_var("seq.post", seq_sort.clone());

            // Precondition: 0 <= i AND i <= len(s) AND n >= 0
            let i_ge_0 = self.ctx.terms.mk_ge(i, zero);
            let i_le_len = self.ctx.terms.mk_le(i, len_s);
            let n_ge_0 = self.ctx.terms.mk_ge(n, zero);
            let valid_cond = self.ctx.terms.mk_and(vec![i_ge_0, i_le_len, n_ge_0]);

            // s = sk_pre ++ e ++ sk_post
            let inner_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![extract_term, sk_post],
                seq_sort.clone(),
            );
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_pre, inner_concat],
                seq_sort.clone(),
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);
            axioms.push(self.ctx.terms.mk_implies(valid_cond, decomp));

            // len(sk_pre) = i  (when valid)
            let len_pre = self.mk_seq_len(sk_pre);
            let iv_ge = self.ctx.terms.mk_ge(i, zero);
            let iv_le = self.ctx.terms.mk_le(i, len_s);
            let i_valid = self.ctx.terms.mk_and(vec![iv_ge, iv_le]);
            let eq_pre_i = self.ctx.terms.mk_eq(len_pre, i);
            axioms.push(self.ctx.terms.mk_implies(i_valid, eq_pre_i));

            // len(e): exact or clamped
            // Case A: len(s) >= n + i => len(e) = n
            let n_plus_i = self.ctx.terms.mk_add(vec![n, i]);
            let ea_ge_i = self.ctx.terms.mk_ge(i, zero);
            let ea_le_i = self.ctx.terms.mk_le(i, len_s);
            let ea_ge_n = self.ctx.terms.mk_ge(n, zero);
            let ea_ge_s = self.ctx.terms.mk_ge(len_s, n_plus_i);
            let exact_cond = self
                .ctx
                .terms
                .mk_and(vec![ea_ge_i, ea_le_i, ea_ge_n, ea_ge_s]);
            let eq_len_n = self.ctx.terms.mk_eq(len_e, n);
            axioms.push(self.ctx.terms.mk_implies(exact_cond, eq_len_n));

            // Case B: len(s) < n + i => len(e) = len(s) - i
            let cb_ge_i = self.ctx.terms.mk_ge(i, zero);
            let cb_le_i = self.ctx.terms.mk_le(i, len_s);
            let cb_ge_n = self.ctx.terms.mk_ge(n, zero);
            let cb_lt_s = self.ctx.terms.mk_lt(len_s, n_plus_i);
            let clamped_cond = self
                .ctx
                .terms
                .mk_and(vec![cb_ge_i, cb_le_i, cb_ge_n, cb_lt_s]);
            let len_s_minus_i = self.ctx.terms.mk_sub(vec![len_s, i]);
            let eq_clamped = self.ctx.terms.mk_eq(len_e, len_s_minus_i);
            axioms.push(self.ctx.terms.mk_implies(clamped_cond, eq_clamped));

            // Out-of-bounds: i < 0 OR i > len(s) OR n <= 0 => e = seq.empty
            let empty = self.mk_seq_empty(&seq_sort);
            let oob_a = self.ctx.terms.mk_lt(i, zero);
            let oob_b = self.ctx.terms.mk_gt(i, len_s);
            let oob_c = self.ctx.terms.mk_le(n, zero);
            let oob = self.ctx.terms.mk_or(vec![oob_a, oob_b, oob_c]);
            let eq_empty = self.ctx.terms.mk_eq(extract_term, empty);
            axioms.push(self.ctx.terms.mk_implies(oob, eq_empty));

            // Inject len(empty) = 0 so OOB reasoning chains correctly.
            // The scan may not have seen this empty term since we just created it.
            let len_empty = self.mk_seq_len(empty);
            axioms.push(self.ctx.terms.mk_eq(len_empty, zero));

            // Non-negativity constraints for generated len terms
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_e, zero));
            axioms.push(self.ctx.terms.mk_ge(len_pre, zero));

            // Full-extract VALUE identity: extract(s, 0, n) = s when n >= len(s).
            //
            // The skolem decomposition above only constrains LENGTHS
            // (len(sk_pre)=i=0, len(e)=n=len(s), len(sk_post)=0); the EUF solver
            // cannot derive `sk_pre = empty`, `sk_post = empty`, and
            // `empty ++ e ++ empty = e`, so the whole-sequence equality
            // `extract = s` stays underivable. A formula like
            // `(= (seq.len s) 3) (not (= (seq.extract s 0 3) s))` is then wrongly
            // SAT (and the seq.nth path builds a model with extract != s).
            // This direct identity closes it. Sound per SMT-LIB: with i = 0 and
            // n >= len(s) the extraction copies all of s.
            //
            // SCOPED to a literal `i = 0` and a literal non-negative `n`: the
            // extracts SYNTHESIZED by indexof/replace reductions are of the form
            // `extract(t, 0, (- (seq.len t) 1))` — a SYMBOLIC `n` — and forcing
            // an `extract = t` equality on those derails their own reduction's
            // model construction (sat/unsat → unknown). User-written
            // full-length extracts use a constant `n`, so the literal guard keeps
            // the refutation power without touching the synthesized terms.
            let i_is_zero = matches!(
                self.ctx.terms.get(i),
                TermData::Const(Constant::Int(v)) if v.is_zero()
            );
            let n_is_nonneg_const = matches!(
                self.ctx.terms.get(n),
                TermData::Const(Constant::Int(v)) if *v >= BigInt::zero()
            );
            if i_is_zero && n_is_nonneg_const {
                let n_ge_len = self.ctx.terms.mk_ge(n, len_s);
                let extract_eq_s = self.ctx.terms.mk_eq(extract_term, s);
                axioms.push(self.ctx.terms.mk_implies(n_ge_len, extract_eq_s));
            }

            // Full-extract identity with a SYMBOLIC length equal to `(seq.len s)`
            // (#seq-extract-whole-symbolic-len): `(seq.extract s 0 (seq.len s))`
            // copies ALL of s, UNCONDITIONALLY — with i = 0 and n = len(s) the
            // out-of-bounds and clamp cases never apply, so the result is exactly
            // s (true even for the empty sequence: extract(empty,0,0) = empty).
            // The literal-`n` branch above cannot see this because here `n` is the
            // `(seq.len s)` TERM, not a constant, so `(not (= (seq.extract a 0
            // (seq.len a)) a))` was wrongly SAT. Scoped to i literally 0 and `n`
            // SYNTACTICALLY the `(seq.len s)` of the SAME base s, so the extracts
            // synthesized by indexof/replace reductions — of the form
            // `extract(t, 0, (- (seq.len t) 1))`, whose `n` is NOT `(seq.len t)` —
            // are untouched. Sound per SMT-LIB (z3 proves the negation unsat).
            if i_is_zero && n == len_s {
                axioms.push(self.ctx.terms.mk_eq(extract_term, s));
            }

            // Length-1 extract IS `seq.at` (#seq-at-as-unit): the frontend
            // desugars `(seq.at s i)` to `(seq.extract s i 1)`, and for an
            // IN-BOUNDS index that singleton is `(seq.unit (seq.nth s i))`. The
            // EUF/length axioms above only pin the extract's LENGTH (to 1); they
            // never link the opaque extract node to the element read, so
            // `(not (= (seq.at a 0) (seq.unit (seq.nth a 0))))` under `0 < len a`,
            // and the `(seq.nth (seq.at a 1) 0)` variant, were wrongly SAT. Emit,
            // guarded by the in-bounds precondition `0 <= i < len(s)`:
            //   (a) extract          = (seq.unit (seq.nth s i))   [content]
            //   (b) (seq.nth e 0)    = (seq.nth s i)              [element read]
            // Both are SMT-LIB theorems (z3 proves each negation unsat). Scoped to
            // a literal length of EXACTLY 1 so only genuine `seq.at` reads match;
            // out of bounds the guard is vacuous (extract is empty there).
            let n_is_one = matches!(
                self.ctx.terms.get(n),
                TermData::Const(Constant::Int(v)) if *v == BigInt::from(1)
            );
            if n_is_one {
                let i_ge_0b = self.ctx.terms.mk_ge(i, zero);
                let i_lt_len = self.ctx.terms.mk_lt(i, len_s);
                let in_bounds = self.ctx.terms.mk_and(vec![i_ge_0b, i_lt_len]);
                let elem_sort = seq_sort
                    .seq_element()
                    .cloned()
                    .unwrap_or(ay_core::Sort::Int);
                let nth_si =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("seq.nth"), vec![s, i], elem_sort.clone());
                let unit_nth = self.ctx.terms.mk_app(
                    Symbol::named("seq.unit"),
                    vec![nth_si],
                    seq_sort.clone(),
                );
                let eq_unit = self.ctx.terms.mk_eq(extract_term, unit_nth);
                axioms.push(self.ctx.terms.mk_implies(in_bounds, eq_unit));

                let nth_e0 = self.ctx.terms.mk_app(
                    Symbol::named("seq.nth"),
                    vec![extract_term, zero],
                    elem_sort,
                );
                let eq_passthrough = self.ctx.terms.mk_eq(nth_e0, nth_si);
                axioms.push(self.ctx.terms.mk_implies(in_bounds, eq_passthrough));
            }
        }

        axioms
    }

    /// Generate `seq.prefixof` axioms (#5841).
    ///
    /// For each `seq.prefixof(s, t)` term `p`:
    /// - Positive: `p => t = s ++ sk_suffix`  (Z3: theory_seq.cpp:3070)
    /// - Positive: `p => len(sk_suffix) >= 0`
    /// - Basic: `p => len(s) <= len(t)`
    ///
    /// Reference: Z3 theory_seq.cpp:3065-3078
    pub(super) fn generate_seq_prefixof_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();

        for &(prefix_term, s, t) in &scan.prefixof_terms {
            let seq_sort = self.ctx.terms.sort(t).clone();

            // Completeness (#6035): ground evaluation for prefixof.
            //
            // When both s and t resolve to concrete sequences (via equality
            // assertions or nth reconstruction), evaluate prefixof directly and
            // force prefixof = true/false. This is AUTHORITATIVE — the forced
            // boolean fully decides the predicate over concrete sequences.
            //
            // When ground-resolved we SKIP the Skolem decomposition below
            // (`continue`), mirroring the seq.extract ground path. The Skolem
            // `t = s ++ sk_suffix` axiom is then redundant (the forced boolean
            // is authoritative) and over a multi-element CONCAT container it only
            // injects an unconstrained fresh Skolem seq var that the combined
            // seq theory cannot reconcile during in-loop model validation,
            // fail-closing an otherwise-SAT model to Unknown (#seq-redundant-skolem).
            //
            // Previous extract-based approach (#6024) caused false-UNSAT (#6033).
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                let is_prefix = s_elems.len() <= t_elems.len()
                    && s_elems
                        .iter()
                        .zip(t_elems.iter())
                        .all(|(&se, &te)| self.ground_seq_elem_eq(se, te));
                if is_prefix {
                    axioms.push(prefix_term); // Force prefixof = true
                } else {
                    let not_p = self.ctx.terms.mk_not(prefix_term);
                    axioms.push(not_p); // Force prefixof = false
                }
                // Skip the redundant Skolem decomposition ONLY when both
                // operands are DIRECTLY ground literals (post-inlining); over a
                // multi-element CONCAT container the Skolem's fresh seq var
                // breaks in-loop validation of an otherwise-SAT model. An
                // nth-RECONSTRUCTED variable source (ground only via the
                // ground_map) keeps the Skolem so it can still build a full
                // in-loop model (mirrors contains, #seq-redundant-skolem / #6028).
                if self.try_extract_ground_seq(s).is_some()
                    && self.try_extract_ground_seq(t).is_some()
                {
                    continue;
                }
            }

            // Skolem: sk_suffix such that prefixof(s, t) => t = s ++ sk_suffix
            let sk_suffix = self
                .ctx
                .terms
                .mk_fresh_var("seq.p.suffix", seq_sort.clone());

            // t = s ++ sk_suffix
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![s, sk_suffix], seq_sort);
            let decomp = self.ctx.terms.mk_eq(t, concat);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, decomp));

            // len(sk_suffix) >= 0
            let len_suffix = self.mk_seq_len(sk_suffix);
            let ge_suffix = self.ctx.terms.mk_ge(len_suffix, zero);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, ge_suffix));

            // prefixof(s, t) => len(s) <= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let le_s_t = self.ctx.terms.mk_le(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(prefix_term, le_s_t));

            // Non-negativity
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_t, zero));
        }

        axioms
    }

    /// Generate `seq.suffixof` axioms (#5841).
    ///
    /// For each `seq.suffixof(s, t)` term `p`:
    /// - Positive: `p => t = sk_prefix ++ s`  (Z3: theory_seq.cpp:3085)
    /// - Positive: `p => len(sk_prefix) >= 0`
    /// - Basic: `p => len(s) <= len(t)`
    ///
    /// Reference: Z3 theory_seq.cpp:3080-3089
    pub(super) fn generate_seq_suffixof_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let ground_map = self.build_ground_seq_map();

        for &(suffix_term, s, t) in &scan.suffixof_terms {
            let seq_sort = self.ctx.terms.sort(t).clone();

            // Completeness (#6035): ground evaluation for suffixof, run FIRST.
            //
            // When both s and t resolve to concrete sequences, force suffixof =
            // true/false directly (authoritative) and SKIP the Skolem
            // decomposition + last-element axioms below. The Skolem
            // `t = sk_prefix ++ s` is redundant once the boolean is forced, and
            // over a multi-element CONCAT container it injects an unconstrained
            // fresh Skolem seq var the combined seq theory cannot reconcile,
            // fail-closing an otherwise-SAT model to Unknown (#seq-redundant-skolem).
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                let is_suffix = s_elems.len() <= t_elems.len()
                    && s_elems
                        .iter()
                        .rev()
                        .zip(t_elems.iter().rev())
                        .all(|(&se, &te)| self.ground_seq_elem_eq(se, te));
                if is_suffix {
                    axioms.push(suffix_term); // Force suffixof = true
                } else {
                    let not_s = self.ctx.terms.mk_not(suffix_term);
                    axioms.push(not_s); // Force suffixof = false
                }
                // Skip the redundant Skolem decomposition ONLY when both
                // operands are DIRECTLY ground literals (post-inlining); over a
                // multi-element CONCAT container the Skolem's fresh seq var
                // breaks in-loop validation of an otherwise-SAT model. An
                // nth-RECONSTRUCTED variable source (ground only via the
                // ground_map) keeps the Skolem so it can still build a full
                // in-loop model (mirrors contains, #seq-redundant-skolem / #6028).
                if self.try_extract_ground_seq(s).is_some()
                    && self.try_extract_ground_seq(t).is_some()
                {
                    continue;
                }
            }

            // Skolem: sk_prefix such that suffixof(s, t) => t = sk_prefix ++ s
            let sk_prefix = self
                .ctx
                .terms
                .mk_fresh_var("seq.s.prefix", seq_sort.clone());

            // t = sk_prefix ++ s
            let concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![sk_prefix, s], seq_sort);
            let decomp = self.ctx.terms.mk_eq(t, concat);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, decomp));

            // len(sk_prefix) >= 0
            let len_prefix = self.mk_seq_len(sk_prefix);
            let ge_prefix = self.ctx.terms.mk_ge(len_prefix, zero);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, ge_prefix));

            // suffixof(s, t) => len(s) <= len(t)
            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let le_s_t = self.ctx.terms.mk_le(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(suffix_term, le_s_t));

            // (#seq-suffixof-last-elem) suffixof(s, t) ∧ len(s) >= 1  =>  the LAST
            // element of s equals the last element of t:
            //   nth(s, len(s)-1) = nth(t, len(t)-1).
            // Sound (a suffix shares its container's tail). Crucially this catches
            // the element-alignment refutation even when t is NOT fully ground: the
            // concat seq.nth decomposition resolves nth(t, len(t)-1) to t's LAST
            // segment regardless of a symbolic prefix (t = v ++ [1]), so a needle
            // whose last element differs (s = [-1,-1] vs t ending in 1) forces
            // -1 = 1 → unsat (fuzzer seq_falsesat_suffixof_elem_mismatch; the prior
            // Skolem-only axioms left it a free word equation AY did not refute).
            let elem_sort = self
                .ctx
                .terms
                .sort(t)
                .seq_element()
                .cloned()
                .unwrap_or(ay_core::Sort::Int);
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let len_s_m1 = self.ctx.terms.mk_sub(vec![len_s, one]);
            let len_t_m1 = self.ctx.terms.mk_sub(vec![len_t, one]);
            let nth_s_last = self.ctx.terms.mk_app(
                Symbol::named("seq.nth"),
                vec![s, len_s_m1],
                elem_sort.clone(),
            );
            let nth_t_last =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.nth"), vec![t, len_t_m1], elem_sort);
            let last_eq = self.ctx.terms.mk_eq(nth_s_last, nth_t_last);
            let s_nonempty = self.ctx.terms.mk_ge(len_s, one);
            let guard = self.ctx.terms.mk_and(vec![suffix_term, s_nonempty]);
            axioms.push(self.ctx.terms.mk_implies(guard, last_eq));

            // Non-negativity
            axioms.push(self.ctx.terms.mk_ge(len_s, zero));
            axioms.push(self.ctx.terms.mk_ge(len_t, zero));
        }

        axioms
    }

    /// Generate contains axioms for a list of `(contains_term, s, t)` tuples.
    ///
    /// Used for synthesized contains terms (e.g. from indexof) that are not
    /// in the original assertion scan (#5998).
    pub(super) fn generate_seq_contains_axioms_for(
        &mut self,
        terms: &[(TermId, TermId, TermId)],
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());

        // Build ground-sequence map for concrete evaluation of these synthesized
        // contains terms (#seq-indexof-alias). Without this, a synthesized
        // `contains(s, t)` (e.g. from indexof) over concrete sequences is never
        // forced true/false, so `!contains => indexof = -1` stays unconstrained
        // and `is_digit(from_int(indexof))` is rubber-stamped SAT even when `t`
        // is not a substring of `s`. The base `generate_seq_contains_axioms`
        // already performs this evaluation for source-level contains terms; the
        // synthesized path needs it too.
        let ground_map = self.build_ground_seq_map();

        for &(contains_term, s, t) in terms {
            let seq_sort = self.ctx.terms.sort(s).clone();

            // === Ground evaluation (#seq-indexof-alias): if both s and t resolve
            // to concrete sequences (via the transitive equality closure), force
            // contains = true/false directly. Sound: ground containment over
            // concrete sequences is decidable and exact.
            let s_ground = ground_map.get(&s).copied().unwrap_or(s);
            let t_ground = ground_map.get(&t).copied().unwrap_or(t);
            if let (Some(s_elems), Some(t_elems)) = (
                self.try_extract_ground_seq(s_ground),
                self.try_extract_ground_seq(t_ground),
            ) {
                if self.ground_seq_contains(&s_elems, &t_elems) {
                    axioms.push(contains_term); // Force contains = true
                } else {
                    let not_c = self.ctx.terms.mk_not(contains_term);
                    axioms.push(not_c); // Force contains = false
                }
            }

            let sk_left = self.ctx.terms.mk_fresh_var("seq.cnt.l", seq_sort.clone());
            let sk_right = self.ctx.terms.mk_fresh_var("seq.cnt.r", seq_sort.clone());

            let inner_concat =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![t, sk_right], seq_sort.clone());
            let full_concat = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_left, inner_concat],
                seq_sort,
            );
            let decomp = self.ctx.terms.mk_eq(s, full_concat);
            axioms.push(self.ctx.terms.mk_implies(contains_term, decomp));

            let len_left = self.mk_seq_len(sk_left);
            let ge_left = self.ctx.terms.mk_ge(len_left, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_left));

            let len_right = self.mk_seq_len(sk_right);
            let ge_right = self.ctx.terms.mk_ge(len_right, zero);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_right));

            let len_s = self.mk_seq_len(s);
            let len_t = self.mk_seq_len(t);
            let ge_len = self.ctx.terms.mk_ge(len_s, len_t);
            axioms.push(self.ctx.terms.mk_implies(contains_term, ge_len));
        }

        axioms
    }

    /// Resolve a predicate's haystack `hay` and ground needle `needle` to a
    /// `(partial_haystack_elements, needle_constants)` pair, when `hay` is a
    /// (possibly partially) determined seq variable (definite length + some pinned
    /// elements) NOT in `ground_map`, and `needle` resolves to a fully ground
    /// sequence. Returns `None` otherwise (#seq-partial-pred).
    ///
    /// A fully-reconstructed haystack (already in `ground_map`) is left to the
    /// authoritative ground-forcing path in the per-predicate generators above.
    /// A haystack that is fully determined ONLY via the endpoint-pin fold
    /// (#seq-pairwise-compat) — pinned by asserted prefixof/suffixof + a length, but
    /// not present in `ground_map` — IS handled here: the three-valued evaluation
    /// then becomes two-valued, which is exactly what refutes a contradictory
    /// contains/prefixof/suffixof over such an s.
    fn partial_pred_operands(
        &self,
        hay: TermId,
        needle: TermId,
        partial: &HashMap<TermId, Vec<Option<TermId>>>,
        ground_map: &HashMap<TermId, TermId>,
    ) -> Option<(Vec<Option<TermId>>, Vec<TermId>)> {
        if ground_map.contains_key(&hay) {
            return None; // fully reconstructed: handled by the ground path
        }
        let elems = partial.get(&hay)?.clone();
        let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
        let needle_units = self.try_extract_ground_seq(needle_g)?;
        let needle_consts: Vec<TermId> = needle_units
            .iter()
            .map(|&u| self.seq_unit_inner_const(u))
            .collect::<Option<Vec<_>>>()?;
        Some((elems, needle_consts))
    }

    /// Three-valued forcing of search predicates over PARTIALLY-determined
    /// sequences (#seq-partial-pred).
    ///
    /// A `prefixof`/`suffixof`/`contains`/`indexof` whose haystack is a seq
    /// VARIABLE with a definite length `(= (seq.len s) N)` and SOME — not
    /// necessarily all — pinned elements `(= (seq.nth s i) c)` is left
    /// under-constrained by the Skolem axioms: a pinned element that CONTRADICTS
    /// the predicate is never connected to it, so the predicate floats free and
    /// the solver reports a wrong SAT (e.g. `len(s)=2 ∧ nth(s,0)=true ∧
    /// prefixof([false], s)` is UNSAT, but `s[1]` is free so full reconstruction
    /// does not fire). This pass evaluates the predicate three-valued against the
    /// pinned elements and forces only the DEFINITE outcomes.
    ///
    /// SOUND: every forced fact is a consequence of the definitely-true
    /// `seq.len`/`seq.nth` constraints (a pinned mismatch makes the predicate
    /// impossible in every model), so the pass can only refute a genuinely
    /// infeasible predicate — never prune a real model (no wrong UNSAT).
    pub(super) fn generate_seq_partial_predicate_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let partial = self.build_partial_seq_element_map();
        if partial.is_empty() {
            return axioms;
        }
        let ground_map = self.build_ground_seq_map();
        let int_const_aliases = self.build_int_const_alias_map();

        // prefixof(needle, hay): needle is a leading window of hay.
        for &(pred_term, needle, hay) in &scan.prefixof_terms {
            let Some((elems, ndl)) = self.partial_pred_operands(hay, needle, &partial, &ground_map)
            else {
                continue;
            };
            let tri = if ndl.len() > elems.len() {
                SeqTri::False
            } else {
                Self::seq_window_tri(&elems, &ndl, 0)
            };
            self.push_pred_force(pred_term, tri, &mut axioms);
        }

        // suffixof(needle, hay): needle is the trailing window of hay.
        for &(pred_term, needle, hay) in &scan.suffixof_terms {
            let Some((elems, ndl)) = self.partial_pred_operands(hay, needle, &partial, &ground_map)
            else {
                continue;
            };
            let tri = if ndl.len() > elems.len() {
                SeqTri::False
            } else {
                Self::seq_window_tri(&elems, &ndl, elems.len() - ndl.len())
            };
            self.push_pred_force(pred_term, tri, &mut axioms);
        }

        // contains(hay, needle): needle occurs at some window of hay.
        for &(pred_term, hay, needle) in &scan.contains_terms {
            let Some((elems, ndl)) = self.partial_pred_operands(hay, needle, &partial, &ground_map)
            else {
                continue;
            };
            let tri = self.contains_partial_tri(&elems, &ndl);
            self.push_pred_force(pred_term, tri, &mut axioms);

            // Unique-window forcing: if `contains` holds and EXACTLY ONE window can
            // possibly match (every other window has a pinned mismatch), the match
            // MUST be at that window, so pin its elements:
            //   contains(hay, q) ⟹ ⋀ nth(hay, start+j) = q[j].
            // SOUND: every non-`start` window is definitely-False (a pinned
            // mismatch), so under `contains` the occurrence can only be at `start`.
            // Guarded by `pred_term`, so it never prunes a model where contains is
            // false (no wrong UNSAT). This lets a forced occurrence feed the
            // prefixof/suffixof element definitions (e.g. a single false in a
            // tail-pinned s forces s[0]=false ⟹ refutes ¬prefixof([false],s)).
            let l = ndl.len();
            if l >= 1 && l <= elems.len() {
                let mut only: Option<usize> = None;
                let mut multiple = false;
                for start in 0..=(elems.len() - l) {
                    if Self::seq_window_tri(&elems, &ndl, start) != SeqTri::False {
                        if only.is_some() {
                            multiple = true;
                            break;
                        }
                        only = Some(start);
                    }
                }
                if let (false, Some(start)) = (multiple, only) {
                    let elem_sort = self
                        .ctx
                        .terms
                        .sort(hay)
                        .seq_element()
                        .cloned()
                        .unwrap_or(ay_core::Sort::Int);
                    for (j, &c) in ndl.iter().enumerate() {
                        let idx = self.ctx.terms.mk_int(BigInt::from(start + j));
                        let nth = self.ctx.terms.mk_app(
                            Symbol::named("seq.nth"),
                            vec![hay, idx],
                            elem_sort.clone(),
                        );
                        let eq = self.ctx.terms.mk_eq(nth, c);
                        axioms.push(self.ctx.terms.mk_implies(pred_term, eq));
                    }
                }
            }
        }

        // indexof(hay, needle, offset): emit the sound necessary facts the Skolem
        // decomposition leaves out — `indexof != p` for every pinned-non-match
        // window p, plus a pinned definite value when fully determined.
        for &(idx_term, hay, needle, offset) in &scan.indexof_terms {
            let Some((elems, ndl)) = self.partial_pred_operands(hay, needle, &partial, &ground_map)
            else {
                continue;
            };
            self.partial_indexof_axioms(
                idx_term,
                &elems,
                &ndl,
                offset,
                &int_const_aliases,
                &mut axioms,
            );
        }

        axioms
    }

    /// Force a boolean predicate term to its DEFINITE three-valued outcome.
    fn push_pred_force(&mut self, pred_term: TermId, tri: SeqTri, axioms: &mut Vec<TermId>) {
        match tri {
            SeqTri::True => axioms.push(pred_term),
            SeqTri::False => {
                let nt = self.ctx.terms.mk_not(pred_term);
                axioms.push(nt);
            }
            SeqTri::Unknown => {}
        }
    }

    /// Three-valued `contains`: `True` if some window is a pinned match, `False`
    /// if EVERY window has a pinned mismatch, else `Unknown`.
    fn contains_partial_tri(&self, elems: &[Option<TermId>], ndl: &[TermId]) -> SeqTri {
        let l = ndl.len();
        if l == 0 {
            return SeqTri::True; // empty needle is always contained
        }
        if l > elems.len() {
            return SeqTri::False;
        }
        let mut saw_unknown = false;
        for p in 0..=(elems.len() - l) {
            match Self::seq_window_tri(elems, ndl, p) {
                SeqTri::True => return SeqTri::True,
                SeqTri::Unknown => saw_unknown = true,
                SeqTri::False => {}
            }
        }
        if saw_unknown {
            SeqTri::Unknown
        } else {
            SeqTri::False
        }
    }

    /// Emit sound `seq.indexof` facts over a partially-determined haystack.
    fn partial_indexof_axioms(
        &mut self,
        idx_term: TermId,
        elems: &[Option<TermId>],
        ndl: &[TermId],
        offset: TermId,
        int_const_aliases: &HashMap<TermId, TermId>,
        axioms: &mut Vec<TermId>,
    ) {
        let n = elems.len();
        let l = ndl.len();
        let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
        // Empty needle: result depends only on offset/length — leave to the main
        // indexof generator (rare; not a wrong-SAT source here).
        if l == 0 {
            return;
        }
        // Needle longer than the (now definite-length) haystack: never found.
        if l > n {
            axioms.push(self.ctx.terms.mk_eq(idx_term, neg_one));
            return;
        }
        // `indexof != p` for every window p with a PINNED non-match: position p is
        // definitely not a match, so the first-match index is never p. Sound
        // irrespective of the search offset.
        for p in 0..=(n - l) {
            if Self::seq_window_tri(elems, ndl, p) == SeqTri::False {
                let p_int = self.ctx.terms.mk_int(BigInt::from(p));
                let eq = self.ctx.terms.mk_eq(idx_term, p_int);
                let ne = self.ctx.terms.mk_not(eq);
                axioms.push(ne);
            }
        }
        // Offset-dependent facts require a literal offset.
        let offset = self.resolve_int_const(offset, int_const_aliases);
        let TermData::Const(Constant::Int(off_val)) = self.ctx.terms.get(offset) else {
            return;
        };
        // Negative offset => result is -1 (SMT-LIB semantics).
        if off_val.sign() == num_bigint::Sign::Minus {
            axioms.push(self.ctx.terms.mk_eq(idx_term, neg_one));
            return;
        }
        let Some(off) = off_val.to_usize() else {
            return;
        };
        if off > n || off > n - l {
            // Offset past the end, or no room for the needle at/after offset:
            // the result is -1.
            axioms.push(self.ctx.terms.mk_eq(idx_term, neg_one));
            return;
        }
        // Range bounds (sound for ANY model): the result is either -1 or a valid
        // start index in `[off, n - l]`. Emitting these refutes a compared value
        // outside that band (e.g. an equality to an index `< off` or `> n - l`).
        let off_int = self.ctx.terms.mk_int(BigInt::from(off));
        let nl_int = self.ctx.terms.mk_int(BigInt::from(n - l));
        let is_neg1 = self.ctx.terms.mk_eq(idx_term, neg_one);
        if off >= 1 {
            let ge_off = self.ctx.terms.mk_ge(idx_term, off_int);
            axioms.push(self.ctx.terms.mk_or(vec![is_neg1, ge_off]));
        }
        let le_nl = self.ctx.terms.mk_le(idx_term, nl_int);
        axioms.push(self.ctx.terms.mk_or(vec![is_neg1, le_nl]));

        // Scan from the offset: classify the search window [off, n-l].
        let mut first_true: Option<usize> = None; // first pinned match >= offset
        let mut first_nonfalse: Option<usize> = None; // first possible match >= offset
        let mut all_false = true; // every window >= offset is a pinned non-match
        for p in off..=(n - l) {
            match Self::seq_window_tri(elems, ndl, p) {
                SeqTri::True => {
                    all_false = false;
                    first_nonfalse.get_or_insert(p);
                    first_true.get_or_insert(p);
                }
                SeqTri::Unknown => {
                    all_false = false;
                    first_nonfalse.get_or_insert(p);
                }
                SeqTri::False => {}
            }
        }
        if let Some(pt) = first_true {
            // A pinned match exists at `pt >= offset`, so the result is found
            // (not -1) and the FIRST match is at or before `pt`: `indexof <= pt`.
            let ne = self.ctx.terms.mk_not(is_neg1);
            axioms.push(ne);
            let pt_int = self.ctx.terms.mk_int(BigInt::from(pt));
            axioms.push(self.ctx.terms.mk_le(idx_term, pt_int));
            // When every earlier window in `[off, pt)` is a pinned non-match, the
            // first match is EXACTLY `pt` — pin the value.
            if first_nonfalse == Some(pt) {
                let pt_int2 = self.ctx.terms.mk_int(BigInt::from(pt));
                axioms.push(self.ctx.terms.mk_eq(idx_term, pt_int2));
            }
        } else if all_false {
            // Every window at/after offset is a pinned non-match => not found.
            axioms.push(self.ctx.terms.mk_eq(idx_term, neg_one));
        }
    }

    /// Cross-predicate compatibility axioms for pairs of `prefixof` (and pairs of
    /// `suffixof`) atoms asserted over the SAME haystack (#seq-pairwise-compat).
    ///
    /// THE WRONG-SAT THIS FIXES: multiple symbolic `prefixof`/`suffixof` atoms over
    /// one free seq variable `s` are never cross-related, so contradictory pins are
    /// wrongly SAT. E.g. `prefixof([1], s) ∧ prefixof([2,2,2], s)` both force
    /// `s[0]`: `s[0]=1` AND `s[0]=2` → UNSAT, but the per-predicate Skolem axioms
    /// (`s = needle ++ sk`) introduce independent suffix Skolems and never connect
    /// the two needles, so AY returns `sat`.
    ///
    /// SOUND FACTS (p1, p2 GROUND needles asserted over the SAME haystack s):
    ///
    /// * MONOTONICITY: if p1 is a prefix of p2 then `prefixof(p2, s) ⟹
    ///   prefixof(p1, s)` (every prefix of a prefix of s is itself a prefix of s).
    ///   This catches the MIXED-POLARITY conflict `prefixof([a,a], s) ∧
    ///   ¬prefixof([a], s)`.
    /// * INCOMPATIBILITY: if NEITHER p1 nor p2 is a prefix of the other, they pin a
    ///   shared index to two different values, so `¬prefixof(p1, s) ∨
    ///   ¬prefixof(p2, s)`.
    ///
    /// Both are the ground-decidable consequences of
    ///   `prefixof(p1, s) ∧ prefixof(p2, s) ⟹ prefixof(p1, p2) ∨ prefixof(p2, p1)`.
    /// Symmetrically for `suffixof` (aligned from the tail). Each emitted clause is
    /// a valid theory lemma for ANY model (independent of the SAT solver's polarity
    /// choice), so it can only refute a genuinely-infeasible combination — never
    /// prune a real model (no wrong UNSAT).
    ///
    /// SCOPE: only GROUND-reconstructible needles (so the prefix/suffix tests are
    /// decidable) sharing the SAME haystack term. `prefixof × suffixof` is
    /// deliberately NOT handled: a short head and a short tail of the same seq only
    /// conflict when their lengths force an overlap (`len(p1)+len(p2) > len(s)`),
    /// which is not derivable for a free `s` — stating it without that guard would
    /// be unsound, so it is skipped.
    pub(super) fn generate_seq_pairwise_compat_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let ground_map = self.build_ground_seq_map();
        self.pairwise_compat_end(
            &scan.prefixof_terms,
            &ground_map,
            CompatEnd::Prefix,
            &mut axioms,
        );
        self.pairwise_compat_end(
            &scan.suffixof_terms,
            &ground_map,
            CompatEnd::Suffix,
            &mut axioms,
        );
        axioms
    }

    /// Emit the pairwise monotonicity / incompatibility clauses for every pair of
    /// `(pred, needle, haystack)` atoms in `terms` that share a haystack and whose
    /// needles are GROUND. See `generate_seq_pairwise_compat_axioms`.
    fn pairwise_compat_end(
        &mut self,
        terms: &[(TermId, TermId, TermId)],
        ground_map: &HashMap<TermId, TermId>,
        end: CompatEnd,
        axioms: &mut Vec<TermId>,
    ) {
        // (pred_term, ground needle element constants, haystack term).
        let mut resolved: Vec<(TermId, Vec<TermId>, TermId)> = Vec::new();
        for &(pred_term, needle, haystack) in terms {
            let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
            if let Some(elems) = self.try_extract_ground_seq(needle_g) {
                resolved.push((pred_term, elems, haystack));
            }
        }
        for i in 0..resolved.len() {
            for j in (i + 1)..resolved.len() {
                if resolved[i].2 != resolved[j].2 {
                    continue; // different haystack: no shared-end constraint
                }
                // i_in_j: needle_i is a prefix/suffix of needle_j (so pred_j ⟹ pred_i).
                let (i_in_j, j_in_i) = {
                    let a = &resolved[i].1;
                    let b = &resolved[j].1;
                    match end {
                        CompatEnd::Prefix => (
                            self.ground_seq_is_prefix(a, b),
                            self.ground_seq_is_prefix(b, a),
                        ),
                        CompatEnd::Suffix => (
                            self.ground_seq_is_suffix(a, b),
                            self.ground_seq_is_suffix(b, a),
                        ),
                    }
                };
                let pi = resolved[i].0;
                let pj = resolved[j].0;
                match (i_in_j, j_in_i) {
                    (true, _) => {
                        // pred_j ⟹ pred_i  (needle_i ⊑ needle_j).
                        axioms.push(self.ctx.terms.mk_implies(pj, pi));
                        if j_in_i {
                            // Equal content: also pred_i ⟹ pred_j (equivalence).
                            axioms.push(self.ctx.terms.mk_implies(pi, pj));
                        }
                    }
                    (false, true) => {
                        // pred_i ⟹ pred_j  (needle_j ⊑ needle_i).
                        axioms.push(self.ctx.terms.mk_implies(pi, pj));
                    }
                    (false, false) => {
                        // Incomparable needles: cannot both be prefixes/suffixes.
                        let not_i = self.ctx.terms.mk_not(pi);
                        let not_j = self.ctx.terms.mk_not(pj);
                        axioms.push(self.ctx.terms.mk_or(vec![not_i, not_j]));
                    }
                }
            }
        }
    }

    /// Element-pinning axioms: a GROUND `prefixof`/`suffixof` needle over a SYMBOLIC
    /// haystack pins the haystack's elements through `seq.nth` (#seq-pairwise-compat).
    ///
    /// THE WRONG-SAT THIS FIXES: `prefixof([c0,c1], s)` forces `s[0]=c0, s[1]=c1`,
    /// but with no definite length the Skolem axiom (`s = needle ++ sk`) never
    /// connects to an external `(= (seq.nth s i) v)` pin, so a contradictory pin
    /// (`s[0]=2` vs `prefixof([1], s)`) is wrongly SAT. (The partial-predicate pass
    /// only fires when `s` has a DEFINITE length.)
    ///
    /// SOUND: `prefixof(p, s) ⟹ len(s) >= len(p)`, so every index `i < len(p)` is
    /// in range and `s[i] = p[i]`; for `suffixof` the tail index
    /// `len(s) - len(p) + i` is likewise in range and equals `p[i]`. Each fact is
    /// guarded by the predicate, so it holds in exactly the models where the
    /// predicate is true — it can never prune a real model (no wrong UNSAT).
    pub(super) fn generate_seq_ground_needle_pins(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let ground_map = self.build_ground_seq_map();
        // Definite lengths (when `(= (seq.len s) N)` is asserted) let suffix pins use
        // a LITERAL tail index that connects via EUF with prefix / external nth pins,
        // independent of the partial map's last-write-wins overwrite.
        let partial = self.build_partial_seq_element_map();

        // prefixof(p, hay): FORWARD pins hay[i]=p[i] for i in 0..k, plus the
        // BACKWARD definition `(len(hay) >= k AND ⋀ hay[i]=p[i]) ⟹ prefixof(p,hay)`.
        // The backward direction is a theory tautology (prefixof ⟺ long enough AND
        // every head element matches) and refutes a NEGATIVE `¬prefixof` whose
        // elements are pinned to match (e.g. `nth(s,0)=c ∧ len(s)>=1 ∧ ¬prefixof([c],s)`).
        for &(pred_term, needle, hay) in &scan.prefixof_terms {
            let Some(elems) = self.ground_needle_over_symbolic_hay(needle, hay, &ground_map) else {
                continue;
            };
            let elem_sort = self
                .ctx
                .terms
                .sort(hay)
                .seq_element()
                .cloned()
                .unwrap_or(ay_core::Sort::Int);
            let k = elems.len();
            let len_hay = self.mk_seq_len(hay);
            let k_int = self.ctx.terms.mk_int(BigInt::from(k));
            let mut guard: Vec<TermId> = vec![self.ctx.terms.mk_ge(len_hay, k_int)];
            let mut ok = true;
            for (i, &u) in elems.iter().enumerate() {
                let Some(c) = self.seq_unit_inner_const(u) else {
                    ok = false;
                    break;
                };
                let idx = self.ctx.terms.mk_int(BigInt::from(i));
                let nth = self.ctx.terms.mk_app(
                    Symbol::named("seq.nth"),
                    vec![hay, idx],
                    elem_sort.clone(),
                );
                let eq = self.ctx.terms.mk_eq(nth, c);
                axioms.push(self.ctx.terms.mk_implies(pred_term, eq)); // forward pin
                guard.push(eq);
            }
            if ok {
                let g = self.ctx.terms.mk_and(guard);
                axioms.push(self.ctx.terms.mk_implies(g, pred_term)); // backward
            }
        }

        // suffixof(p, hay): hay[N - len(p) + i] = p[i], where N is hay's DEFINITE
        // length. Without a definite length the tail index is symbolic and would not
        // connect with literal-indexed pins, so we only pin in the definite case
        // (the symbolic tail is still covered by the suffixof generator's
        // last-element axiom and the partial-predicate pass).
        for &(pred_term, needle, hay) in &scan.suffixof_terms {
            let Some(elems) = self.ground_needle_over_symbolic_hay(needle, hay, &ground_map) else {
                continue;
            };
            let Some(&n) = partial.get(&hay).map(|v| v.len()).as_ref() else {
                continue; // no definite length
            };
            let l = elems.len();
            if l > n {
                continue; // suffix longer than hay: refuted by the partial-pred pass
            }
            let elem_sort = self
                .ctx
                .terms
                .sort(hay)
                .seq_element()
                .cloned()
                .unwrap_or(ay_core::Sort::Int);
            // BACKWARD definition (definite length N): `(len(hay)=N AND ⋀ the last l
            // elements match p) ⟹ suffixof(p, hay)` — a theory tautology that refutes
            // a NEGATIVE `¬suffixof` whose tail elements are pinned to match.
            let len_hay = self.mk_seq_len(hay);
            let n_int = self.ctx.terms.mk_int(BigInt::from(n));
            let mut guard: Vec<TermId> = vec![self.ctx.terms.mk_eq(len_hay, n_int)];
            let mut ok = true;
            for (i, &u) in elems.iter().enumerate() {
                let Some(c) = self.seq_unit_inner_const(u) else {
                    ok = false;
                    break;
                };
                let idx = self.ctx.terms.mk_int(BigInt::from(n - l + i));
                let nth = self.ctx.terms.mk_app(
                    Symbol::named("seq.nth"),
                    vec![hay, idx],
                    elem_sort.clone(),
                );
                let eq = self.ctx.terms.mk_eq(nth, c);
                axioms.push(self.ctx.terms.mk_implies(pred_term, eq)); // forward pin
                guard.push(eq);
            }
            if ok {
                let g = self.ctx.terms.mk_and(guard);
                axioms.push(self.ctx.terms.mk_implies(g, pred_term)); // backward
            }
        }

        axioms
    }

    /// Cross axioms relating ground `prefixof`/`suffixof`/`contains` needles over the
    /// SAME haystack (#seq-pairwise-compat).
    ///
    /// SOUND FACTS (all are substring-monotonicity of containment):
    /// * `prefixof(p, s) ⟹ contains(s, q)` when q is a contiguous substring of p
    ///   (p is a substring of s, hence so is any substring of p). Same for suffixof.
    /// * `contains(s, p) ⟹ contains(s, q)` when q is a contiguous substring of p.
    ///
    /// These refute an asserted `¬contains(s, q)` alongside a positive
    /// prefixof/suffixof/contains whose ground needle covers q — including cases with
    /// NO definite length, which the partial-predicate pass cannot see. Each is
    /// guarded by the positive antecedent, so it holds exactly in the models where
    /// that antecedent is true (no wrong UNSAT).
    pub(super) fn generate_seq_endpoint_contains_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let ground_map = self.build_ground_seq_map();

        // (endpoint_pred_term, ground needle elements, haystack term).
        let mut endpoints: Vec<(TermId, Vec<TermId>, TermId)> = Vec::new();
        for &(pred, needle, hay) in scan.prefixof_terms.iter().chain(scan.suffixof_terms.iter()) {
            let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
            if let Some(p) = self.try_extract_ground_seq(needle_g) {
                endpoints.push((pred, p, hay));
            }
        }

        // (contains_term, ground needle elements, haystack term).
        let mut contains_g: Vec<(TermId, Vec<TermId>, TermId)> = Vec::new();
        for &(cterm, hay, needle) in &scan.contains_terms {
            let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
            if let Some(q) = self.try_extract_ground_seq(needle_g) {
                contains_g.push((cterm, q, hay));
            }
        }

        // prefixof/suffixof(p, s) ⟹ contains(s, q) when q ⊆ p.
        for (cterm, q, c_hay) in &contains_g {
            for (pred, p, p_hay) in &endpoints {
                if *p_hay == *c_hay && self.ground_seq_contains(p, q) {
                    axioms.push(self.ctx.terms.mk_implies(*pred, *cterm));
                }
            }
        }

        // contains(s, p) ⟹ contains(s, q) when q is a contiguous substring of p.
        for i in 0..contains_g.len() {
            for j in 0..contains_g.len() {
                if i == j || contains_g[i].2 != contains_g[j].2 {
                    continue;
                }
                if self.ground_seq_contains(&contains_g[i].1, &contains_g[j].1) {
                    let (ci, cj) = (contains_g[i].0, contains_g[j].0);
                    axioms.push(self.ctx.terms.mk_implies(ci, cj));
                }
            }
        }

        axioms
    }

    /// `seq.contains` forced TRUE from a window of asserted `seq.nth` pins
    /// (#seq-pairwise-compat).
    ///
    /// THE WRONG-SAT THIS FIXES: `nth(s,i)=c` pins element `i`, so when that index is
    /// in range `s` contains `[c]` — yet `¬contains(s,[c])` may be wrongly SAT
    /// because the per-contains Skolem decomposition never connects to the external
    /// nth pin (no definite length, so the partial-pred pass does not fire).
    ///
    /// For each `contains(s, q)` with a ground q, if asserted nth pins cover some
    /// window `[start, start+|q|)` matching q, emit
    ///   `(nth(s,start)=q0 ∧ … ∧ nth(s,start+|q|-1)=q_{|q|-1} ∧ len(s) >= start+|q|)
    ///        ⟹ contains(s, q)`.
    /// This is a theory tautology (those elements at in-range positions make q occur
    /// at `start`), so it is sound regardless of the assertions — it can only refute
    /// an infeasible `¬contains` (no wrong UNSAT). The `len(s) >= …` conjunct is the
    /// in-range guard: an out-of-range `seq.nth` is unspecified and must not be
    /// treated as an element of s.
    pub(super) fn generate_seq_contains_from_pins_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let ground_map = self.build_ground_seq_map();
        let pin_map = self.collect_asserted_nth_pins();
        if pin_map.is_empty() {
            return axioms;
        }

        for &(contains_term, hay, needle) in &scan.contains_terms {
            // Symbolic haystack only — ground/reconstructed are handled authoritatively.
            let hay_g = ground_map.get(&hay).copied().unwrap_or(hay);
            if self.try_extract_ground_seq(hay_g).is_some() {
                continue;
            }
            let Some(pins) = pin_map.get(&hay) else {
                continue;
            };
            let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
            let Some(units) = self.try_extract_ground_seq(needle_g) else {
                continue;
            };
            let Some(q) = units
                .iter()
                .map(|&u| self.seq_unit_inner_const(u))
                .collect::<Option<Vec<TermId>>>()
            else {
                continue;
            };
            let l = q.len();
            if l == 0 {
                continue;
            }
            // Find a window [start, start+l) fully covered by matching pins.
            let mut window_start = None;
            for &start in pins.keys() {
                if (0..l).all(|j| pins.get(&(start + j)) == Some(&q[j])) {
                    window_start = Some(start);
                    break;
                }
            }
            let Some(start) = window_start else {
                continue;
            };
            let elem_sort = self
                .ctx
                .terms
                .sort(hay)
                .seq_element()
                .cloned()
                .unwrap_or(ay_core::Sort::Int);
            let mut guard: Vec<TermId> = Vec::with_capacity(l + 1);
            for (j, &c) in q.iter().enumerate() {
                let idx = self.ctx.terms.mk_int(BigInt::from(start + j));
                let nth = self.ctx.terms.mk_app(
                    Symbol::named("seq.nth"),
                    vec![hay, idx],
                    elem_sort.clone(),
                );
                guard.push(self.ctx.terms.mk_eq(nth, c));
            }
            let len_hay = self.mk_seq_len(hay);
            let need = self.ctx.terms.mk_int(BigInt::from(start + l));
            guard.push(self.ctx.terms.mk_ge(len_hay, need));
            let g = self.ctx.terms.mk_and(guard);
            axioms.push(self.ctx.terms.mk_implies(g, contains_term));
        }

        axioms
    }

    /// Collect asserted-true `seq.nth` element pins per seq variable, NOT requiring a
    /// definite length: `var -> { index -> const }` from top-level
    /// `(= (seq.nth s i) c)` and the Bool-rewritten `(seq.nth s i)` /
    /// `(not (seq.nth s i))` forms. Each is a definitely-true element fact.
    fn collect_asserted_nth_pins(&mut self) -> HashMap<TermId, HashMap<usize, TermId>> {
        let mut out: HashMap<TermId, HashMap<usize, TermId>> = HashMap::default();
        let true_t = self.ctx.terms.mk_bool(true);
        let false_t = self.ctx.terms.mk_bool(false);

        let record = |terms: &ay_core::term::TermStore,
                      nth_term: TermId,
                      val: TermId,
                      out: &mut HashMap<TermId, HashMap<usize, TermId>>| {
            if let TermData::App(Symbol::Named(name), args) = terms.get(nth_term) {
                if name == "seq.nth"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(..))
                {
                    if let TermData::Const(Constant::Int(iv)) = terms.get(args[1]) {
                        if let Some(i) = iv.to_usize() {
                            out.entry(args[0]).or_default().insert(i, val);
                        }
                    }
                }
            }
        };

        for &assertion in &self.ctx.assertions {
            match self.ctx.terms.get(assertion) {
                // Bool-element forms: (seq.nth s i) => true ; (not (seq.nth s i)) => false.
                TermData::Not(inner) => record(&self.ctx.terms, *inner, false_t, &mut out),
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    let (a, b) = (args[0], args[1]);
                    if matches!(self.ctx.terms.get(b), TermData::Const(..)) {
                        record(&self.ctx.terms, a, b, &mut out);
                    }
                    if matches!(self.ctx.terms.get(a), TermData::Const(..)) {
                        record(&self.ctx.terms, b, a, &mut out);
                    }
                }
                _ => record(&self.ctx.terms, assertion, true_t, &mut out),
            }
        }
        out
    }

    /// Bounded joint-placement refutation for `seq.contains` over a DEFINITE-length
    /// haystack (#seq-pairwise-compat / contains packing).
    ///
    /// THE WRONG-SAT THIS FIXES: several positive `contains(s, q_k)` with ground
    /// needles that cannot simultaneously fit, as contiguous blocks, into an s of a
    /// fixed length N (with its pinned elements) — e.g. two length-4 needles in a
    /// length-5 s must overlap in ≥3 positions and disagree. The per-contains Skolem
    /// decomposition reasons about each occurrence independently, so the joint
    /// infeasibility is missed and the conjunction is wrongly SAT.
    ///
    /// For each seq variable with a definite length N (from the partial map) and a
    /// set C of ASSERTED-TRUE ground-needle contains atoms, we backtrack over every
    /// start position of every needle, checking consistency against the definite
    /// pinned elements and against the other needles' chosen positions. If NO
    /// combined placement is consistent, the conjunction `⋀ C` is infeasible in every
    /// model (the pins + length are definite facts), so we emit `⋁ ¬c_k`.
    ///
    /// SOUND: a refutation is emitted ONLY when an exhaustive placement search proves
    /// infeasibility, so it can never prune a real model (no wrong UNSAT). Bounded by
    /// a cap on N, |C|, and the placement product to keep generation cheap.
    pub(super) fn generate_seq_contains_packing_axioms(&mut self) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let partial = self.build_partial_seq_element_map();
        if partial.is_empty() {
            return axioms;
        }

        // Asserted-true ground-needle contains atoms grouped by definite-length hay.
        let mut by_hay: HashMap<TermId, Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "seq.contains" || args.len() != 2 {
                continue;
            }
            let (hay, needle) = (args[0], args[1]);
            if !partial.contains_key(&hay) {
                continue; // only haystacks with a definite length
            }
            let Some(units) = self.try_extract_ground_seq(needle) else {
                continue;
            };
            let Some(consts) = units
                .iter()
                .map(|&u| self.seq_unit_inner_const(u))
                .collect::<Option<Vec<TermId>>>()
            else {
                continue;
            };
            if consts.is_empty() {
                continue;
            }
            let entry = by_hay.entry(hay).or_default();
            if !entry.iter().any(|(c, _)| *c == assertion) {
                entry.push((assertion, consts));
            }
        }

        for (hay, clist) in &by_hay {
            if clist.len() < 2 {
                continue; // a single contains is covered by the partial-pred pass
            }
            let pins = &partial[hay];
            let n = pins.len();
            if n == 0 || n > 16 || clist.len() > 6 {
                continue; // keep the search cheap
            }
            // Placement product bound.
            let mut product: u64 = 1;
            let mut too_big = false;
            for (_, q) in clist.iter() {
                if q.len() > n {
                    // A needle longer than hay can never occur: the partial-pred /
                    // contains-length axioms already refute it; skip here.
                    too_big = true;
                    break;
                }
                product = product.saturating_mul((n - q.len() + 1) as u64);
                if product > 100_000 {
                    too_big = true;
                    break;
                }
            }
            if too_big {
                continue;
            }
            if !Self::contains_set_placeable(n, pins, clist) {
                let lits: Vec<TermId> = clist
                    .iter()
                    .map(|(cterm, _)| self.ctx.terms.mk_not(*cterm))
                    .collect();
                axioms.push(self.ctx.terms.mk_or(lits));
            }
        }

        axioms
    }

    /// True if there is SOME assignment of start positions for every needle in
    /// `clist` such that all needles (as contiguous blocks) agree with each other
    /// and with the definite `pins` over a length-`n` sequence. Exhaustive backtrack.
    fn contains_set_placeable(
        n: usize,
        pins: &[Option<TermId>],
        clist: &[(TermId, Vec<TermId>)],
    ) -> bool {
        let mut assign: Vec<Option<TermId>> = pins.to_vec();
        Self::place_contains_rec(n, &mut assign, clist, 0)
    }

    fn place_contains_rec(
        n: usize,
        assign: &mut [Option<TermId>],
        clist: &[(TermId, Vec<TermId>)],
        k: usize,
    ) -> bool {
        if k == clist.len() {
            return true; // every needle placed consistently
        }
        let q = &clist[k].1;
        let l = q.len();
        if l > n {
            return false;
        }
        for start in 0..=(n - l) {
            let mut changed: Vec<usize> = Vec::new();
            let mut ok = true;
            for (j, &c) in q.iter().enumerate() {
                let idx = start + j;
                match assign[idx] {
                    Some(existing) => {
                        if existing != c {
                            ok = false;
                            break;
                        }
                    }
                    None => {
                        assign[idx] = Some(c);
                        changed.push(idx);
                    }
                }
            }
            if ok && Self::place_contains_rec(n, assign, clist, k + 1) {
                for &idx in &changed {
                    assign[idx] = None;
                }
                return true;
            }
            for &idx in &changed {
                assign[idx] = None;
            }
        }
        false
    }

    /// Resolve `needle` to its ground element list when it is GROUND and `hay` is a
    /// SYMBOLIC haystack (NOT itself ground-reconstructible — those are decided by
    /// the authoritative ground-evaluation path in the per-predicate generators).
    fn ground_needle_over_symbolic_hay(
        &self,
        needle: TermId,
        hay: TermId,
        ground_map: &HashMap<TermId, TermId>,
    ) -> Option<Vec<TermId>> {
        let hay_g = ground_map.get(&hay).copied().unwrap_or(hay);
        if self.try_extract_ground_seq(hay_g).is_some() {
            return None; // ground haystack: handled authoritatively elsewhere
        }
        let needle_g = ground_map.get(&needle).copied().unwrap_or(needle);
        let elems = self.try_extract_ground_seq(needle_g)?;
        if elems.is_empty() {
            return None; // empty needle pins nothing
        }
        Some(elems)
    }

    /// True if ground sequence `a` is a prefix of ground sequence `b` (both lists
    /// of `seq.unit(constant)` element TermIds), compared element-wise from index 0.
    fn ground_seq_is_prefix(&self, a: &[TermId], b: &[TermId]) -> bool {
        a.len() <= b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(&x, &y)| self.ground_seq_elem_eq(x, y))
    }

    /// True if ground sequence `a` is a suffix of ground sequence `b`, compared
    /// element-wise from the tail.
    fn ground_seq_is_suffix(&self, a: &[TermId], b: &[TermId]) -> bool {
        a.len() <= b.len()
            && a.iter()
                .rev()
                .zip(b.iter().rev())
                .all(|(&x, &y)| self.ground_seq_elem_eq(x, y))
    }
}
