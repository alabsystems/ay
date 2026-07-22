// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String lemma clause creation: translates symbolic `StringLemma` requests into
//! concrete CNF clauses for the SAT solver.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, StringLemma, StringLemmaKind, TermId};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::guards::{build_reason_guard, emit_guard_empty_splits};

/// Deterministically constructed pieces of the `str.indexof` reduction
/// (CAP-2), shared between clause creation and reduced-term marking.
struct IndexofReductionParts {
    /// Needle argument `w`.
    w: TermId,
    /// Offset argument `n`.
    n: TermId,
    /// `(str.len s)` for the haystack argument.
    len_s: TermId,
    /// `Some(value)` when the needle is a string literal.
    const_w: Option<String>,
    /// Search window: `s` itself when `n` is the literal 0, otherwise
    /// `(str.substr s n (- (str.len s) n))`.
    window: TermId,
    /// `(io_pre, io_suf)` window decomposition skolems; `None` for the
    /// empty-constant-needle short circuit (no decomposition needed).
    skolems: Option<(TermId, TermId)>,
    /// `(contains(window, w), contains(io_pre ++ w[0..|w|-1], w))` guard
    /// atoms; `None` for the empty-constant-needle short circuit.
    guards: Option<(TermId, TermId)>,
}

/// Deterministically constructed pieces of the `str.replace` reduction
/// (CAP-2 follow-on), shared between clause creation and reduced-term marking.
struct ReplaceReductionParts {
    /// Haystack argument `s`.
    s: TermId,
    /// Needle argument `t`.
    t: TermId,
    /// Replacement argument `u`.
    u: TermId,
    /// `Some(value)` when the needle is a string literal.
    const_t: Option<String>,
    /// `(rp_pre, rp_suf)` decomposition skolems; `None` for the
    /// empty-constant-needle short circuit (`replace(s, "", u) = u ++ s`).
    skolems: Option<(TermId, TermId)>,
    /// `(contains(s, t), contains(rp_pre ++ t[0..|t|-1], t))` guard atoms;
    /// `None` for the empty-constant-needle short circuit.
    guards: Option<(TermId, TermId)>,
}

/// Deterministically constructed pieces of the `str.replace_all` one-step
/// reduction (extf wave 2), shared between clause creation and reduced-term
/// marking.
struct ReplaceAllReductionParts {
    /// Haystack argument `s`.
    s: TermId,
    /// Needle argument `t`.
    t: TermId,
    /// Replacement argument `u`.
    u: TermId,
    /// `Some(value)` when the needle is a string literal.
    const_t: Option<String>,
    /// `(rpa_pre, rpa_suf)` decomposition skolems plus the recursive
    /// `replace_all(rpa_suf, t, u)` application; `None` for the
    /// empty-constant-needle short circuit (`replace_all(s, "", u) = s`).
    skolems: Option<(TermId, TermId, TermId)>,
    /// `(contains(s, t), contains(rpa_pre ++ t[0..|t|-1], t))` guard atoms;
    /// `None` for the empty-constant-needle short circuit.
    guards: Option<(TermId, TermId)>,
}

impl Executor {
    /// Extra terms that should be marked as dynamically reduced after a string lemma.
    pub(in crate::executor) fn string_lemma_reduced_terms(
        &mut self,
        lemma: &StringLemma,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Vec<TermId> {
        match lemma.kind {
            StringLemmaKind::SubstrReduction => {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if name != "str.substr" || args.len() != 3 {
                    return Vec::new();
                }
                let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, lemma.x);
                let skt = skolem_cache.substr_result(&mut self.ctx.terms, lemma.x);
                let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, lemma.x);
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, skt, sk_suf],
                    Sort::String,
                );
                vec![lemma.x, concat]
            }
            StringLemmaKind::IndexofReduction => {
                // The indexof application is captured by the reduction axioms.
                // The generated contains guard atoms (window containment +
                // leftmost guard) are also marked: they are internal to the
                // reduction — treating them as unresolved extf predicates
                // would re-latch `incomplete` and defeat the reduction. Their
                // semantics stay enforced by the emitted clauses plus the
                // final model-validation chokepoint.
                let Some(parts) = self.indexof_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let mut reduced = vec![lemma.x];
                if let Some((contains_atom, leftmost_ctn)) = parts.guards {
                    reduced.push(contains_atom);
                    reduced.push(leftmost_ctn);
                }
                reduced
            }
            StringLemmaKind::ReplaceReduction => {
                // Same guard-marking rationale as IndexofReduction.
                let Some(parts) = self.replace_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let mut reduced = vec![lemma.x];
                if let Some((contains_atom, leftmost_ctn)) = parts.guards {
                    reduced.push(contains_atom);
                    reduced.push(leftmost_ctn);
                }
                reduced
            }
            StringLemmaKind::ReplaceAllReduction => {
                // Same guard-marking rationale as IndexofReduction. The
                // recursive replace_all(suf, t, u) application is
                // deliberately NOT marked: it must stay unreduced so a later
                // CEGAR round requests its own one-step reduction (or falls
                // back to incomplete once the budget is exhausted).
                let Some(parts) = self.replace_all_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let mut reduced = vec![lemma.x];
                if let Some((contains_atom, leftmost_ctn)) = parts.guards {
                    reduced.push(contains_atom);
                    reduced.push(leftmost_ctn);
                }
                reduced
            }
            // ToIntReduction / FromIntReduction: only the application itself
            // is captured by the reduction axioms. FromIntReduction's inner
            // to_int(r) application intentionally stays unreduced — if it
            // cannot be resolved or reduced later, the solver honestly
            // reports Unknown instead of trusting an unconstrained value.
            //
            // ReplaceRe(All)Reduction: the application is marked so the extf
            // passes stop latching incomplete; the membership guard atom is
            // NOT marked — an unresolved membership must keep latching the
            // regexp solver's incompleteness for honest Unknowns.
            StringLemmaKind::ToIntReduction
            | StringLemmaKind::FromIntReduction
            | StringLemmaKind::ReplaceReReduction
            | StringLemmaKind::ReplaceReAllReduction => {
                vec![lemma.x]
            }
            _ => Vec::new(),
        }
    }

    /// Build the leftmost-guard contains atom for a first-occurrence
    /// decomposition: `contains(pre ++ needle[0..|needle|-1], needle)`. Every
    /// occurrence of the needle starting strictly before the match position
    /// lies entirely inside that string, so asserting the atom FALSE forces
    /// the decomposition to name the FIRST occurrence.
    ///
    /// `const_needle` folds the needle prefix at build time when the needle
    /// is a string literal (single-char needles collapse to `pre` itself).
    fn first_occurrence_leftmost_atom(
        &mut self,
        pre: TermId,
        needle: TermId,
        const_needle: Option<&str>,
    ) -> TermId {
        let leftmost_hay = if let Some(cw) = const_needle {
            let mut chars: Vec<char> = cw.chars().collect();
            chars.pop();
            if chars.is_empty() {
                // Single-char needle: pre ++ "" = pre.
                pre
            } else {
                let pre_w_const: String = chars.into_iter().collect();
                let pre_w = self.ctx.terms.mk_string(pre_w_const);
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.++"), vec![pre, pre_w], Sort::String)
            }
        } else {
            let len_w = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![needle], Sort::Int);
            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let len_w_minus_1 = self.ctx.terms.mk_sub(vec![len_w, one]);
            let pre_w = self.ctx.terms.mk_app(
                Symbol::named("str.substr"),
                vec![needle, zero, len_w_minus_1],
                Sort::String,
            );
            self.ctx
                .terms
                .mk_app(Symbol::named("str.++"), vec![pre, pre_w], Sort::String)
        };
        self.ctx.terms.mk_app(
            Symbol::named("str.contains"),
            vec![leftmost_hay, needle],
            Sort::Bool,
        )
    }

    /// Shared construction for the `str.replace` reduction (CAP-2 follow-on).
    ///
    /// Deterministic for the same reason as `indexof_reduction_parts`.
    fn replace_reduction_parts(
        &mut self,
        replace_term: TermId,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Option<ReplaceReductionParts> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(replace_term) else {
            return None;
        };
        if name != "str.replace" || args.len() != 3 {
            return None;
        }
        let s = args[0];
        let t = args[1];
        let u = args[2];

        let const_t: Option<String> = match self.ctx.terms.get(t) {
            TermData::Const(Constant::String(ct)) => Some(ct.clone()),
            _ => None,
        };

        // Empty constant needle: replace(s, "", u) = u ++ s. No skolems.
        if const_t.as_deref() == Some("") {
            return Some(ReplaceReductionParts {
                s,
                t,
                u,
                const_t,
                skolems: None,
                guards: None,
            });
        }

        let rp_pre = skolem_cache.replace_pre(&mut self.ctx.terms, replace_term);
        let rp_suf = skolem_cache.replace_suffix(&mut self.ctx.terms, replace_term);

        let leftmost_ctn = self.first_occurrence_leftmost_atom(rp_pre, t, const_t.as_deref());
        let contains_atom =
            self.ctx
                .terms
                .mk_app(Symbol::named("str.contains"), vec![s, t], Sort::Bool);

        Some(ReplaceReductionParts {
            s,
            t,
            u,
            const_t,
            skolems: Some((rp_pre, rp_suf)),
            guards: Some((contains_atom, leftmost_ctn)),
        })
    }

    /// Shared construction for the `str.replace_all` one-step reduction
    /// (extf wave 2).
    ///
    /// Deterministic for the same reason as `indexof_reduction_parts`:
    /// interning plus the keyed skolem cache guarantee both callers observe
    /// identical `TermId`s regardless of call order.
    fn replace_all_reduction_parts(
        &mut self,
        replace_all_term: TermId,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Option<ReplaceAllReductionParts> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(replace_all_term) else {
            return None;
        };
        if name != "str.replace_all" || args.len() != 3 {
            return None;
        }
        let s = args[0];
        let t = args[1];
        let u = args[2];

        let const_t: Option<String> = match self.ctx.terms.get(t) {
            TermData::Const(Constant::String(ct)) => Some(ct.clone()),
            _ => None,
        };

        // Empty constant needle: replace_all(s, "", u) = s UNCHANGED
        // (differs from str.replace, which yields u ++ s). No skolems.
        if const_t.as_deref() == Some("") {
            return Some(ReplaceAllReductionParts {
                s,
                t,
                u,
                const_t,
                skolems: None,
                guards: None,
            });
        }

        let rpa_pre = skolem_cache.replace_all_pre(&mut self.ctx.terms, replace_all_term);
        let rpa_suf = skolem_cache.replace_all_suffix(&mut self.ctx.terms, replace_all_term);
        // Recursive application on the suffix: reduced on demand in a later
        // CEGAR round (budget-bounded by the string core).
        let rest = self.ctx.terms.mk_app(
            Symbol::named("str.replace_all"),
            vec![rpa_suf, t, u],
            Sort::String,
        );

        let leftmost_ctn = self.first_occurrence_leftmost_atom(rpa_pre, t, const_t.as_deref());
        let contains_atom =
            self.ctx
                .terms
                .mk_app(Symbol::named("str.contains"), vec![s, t], Sort::Bool);

        Some(ReplaceAllReductionParts {
            s,
            t,
            u,
            const_t,
            skolems: Some((rpa_pre, rpa_suf, rest)),
            guards: Some((contains_atom, leftmost_ctn)),
        })
    }

    /// Shared construction for the `str.indexof` reduction (CAP-2).
    ///
    /// Deterministic: interning + the keyed skolem cache guarantee both
    /// callers (`create_string_lemma_clauses`, `string_lemma_reduced_terms`)
    /// observe identical `TermId`s regardless of call order.
    fn indexof_reduction_parts(
        &mut self,
        indexof_term: TermId,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Option<IndexofReductionParts> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(indexof_term) else {
            return None;
        };
        if name != "str.indexof" || args.len() != 3 {
            return None;
        }
        let s = args[0];
        let w = args[1];
        let n = args[2];

        let len_s = self
            .ctx
            .terms
            .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

        let const_w: Option<String> = match self.ctx.terms.get(w) {
            TermData::Const(Constant::String(cw)) => Some(cw.clone()),
            _ => None,
        };

        // Empty constant needle: no window decomposition, no guards.
        if const_w.as_deref() == Some("") {
            return Some(IndexofReductionParts {
                w,
                n,
                len_s,
                const_w,
                window: s,
                skolems: None,
                guards: None,
            });
        }

        // Search window st = substr(s, n, len(s) - n); shortcut st = s when n
        // is the literal 0 (substr(s, 0, len(s)) = s for every s).
        let window = if matches!(
            self.ctx.terms.get(n),
            TermData::Const(Constant::Int(v)) if v == &BigInt::from(0)
        ) {
            s
        } else {
            let window_len = self.ctx.terms.mk_sub(vec![len_s, n]);
            self.ctx.terms.mk_app(
                Symbol::named("str.substr"),
                vec![s, n, window_len],
                Sort::String,
            )
        };

        let io_pre = skolem_cache.indexof_pre(&mut self.ctx.terms, indexof_term);
        let io_suf = skolem_cache.indexof_suffix(&mut self.ctx.terms, indexof_term);

        // Leftmost guard: every occurrence of w starting strictly before the
        // match lies entirely inside io_pre ++ w[0..|w|-1].
        let leftmost_ctn = self.first_occurrence_leftmost_atom(io_pre, w, const_w.as_deref());
        let contains_atom =
            self.ctx
                .terms
                .mk_app(Symbol::named("str.contains"), vec![window, w], Sort::Bool);

        Some(IndexofReductionParts {
            w,
            n,
            len_s,
            const_w,
            window,
            skolems: Some((io_pre, io_suf)),
            guards: Some((contains_atom, leftmost_ctn)),
        })
    }

    /// Create clauses from a `StringLemma` request.
    ///
    /// Translates the symbolic lemma description into concrete `TermId` atoms.
    /// Returns one or more clauses; the SAT solver must satisfy at least one
    /// literal in each clause.
    ///
    /// - **LengthSplit**: `[len(x) = len(y), ¬(len(x) = len(y))]`
    /// - **EmptySplit**: `[x = "", ¬(x = "")]`
    /// - **ConstSplit** (SSPLIT_CST): `[x = "", x = str.++(c[0], k)]`
    ///   where `c[0]` is the first character of constant `y`, `k` is a fresh
    ///   skolem. The `x = ""` guard prevents over-constraining the empty branch.
    ///   Plus auxiliary: `len(k) >= 0`.
    ///   Reference: CVC5 `core_solver.cpp:1618-1639`, `getConclusion` CONCAT_CSPLIT.
    /// - **VarSplit** (SSPLIT_VAR): `[len(x)=len(y), x = str.++(y, k), y = str.++(x, k)]`
    ///   where `k` is a fresh skolem. The `len(x)=len(y)` guard prevents
    ///   over-constraining the equal-length branch (#3375).
    ///   Plus auxiliary: `len(k) >= 0`.
    ///   Reference: CVC5 `core_solver.cpp:1642-1747`, `getConclusion` CONCAT_SPLIT.
    pub(in crate::executor) fn create_string_lemma_clauses(
        &mut self,
        lemma: &StringLemma,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Vec<Vec<TermId>> {
        match lemma.kind {
            StringLemmaKind::LengthSplit => {
                // Case 6: introduce len(x) = len(y) as a decision atom.
                let len_x =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.x], Sort::Int);
                let len_y =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.y], Sort::Int);
                let eq = self.ctx.terms.mk_eq(len_x, len_y);
                let neq = self.ctx.terms.mk_not(eq);
                vec![vec![eq, neq]]
            }
            StringLemmaKind::EmptySplit => {
                // Case 8 prerequisite: introduce x = "" as a decision atom.
                let empty = self.ctx.terms.mk_string(String::new());
                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                let neq = self.ctx.terms.mk_not(eq);
                vec![vec![eq, neq]]
            }
            StringLemmaKind::ConstSplit => {
                // SSPLIT_CST: x = "" OR x = char_at(y, char_offset) ++ k.
                //
                // Guard: ConstSplit is only valid when x != "". We add `x = ""`
                // as an escape literal so that when SAT backtracks to x = "",
                // the clause is trivially satisfied and the skolem k is
                // unconstrained (#3375).
                //
                // Extract the character at `char_offset` of constant y.
                // When char_offset > 0, the constant has already been partially
                // consumed by process_simple_neq's offset tracking.
                let first_char = match self.ctx.terms.get(lemma.y) {
                    TermData::Const(Constant::String(s)) => {
                        debug_assert!(
                            lemma.char_offset < s.chars().count(),
                            "BUG: ConstSplit char_offset {} >= constant y length {} — NF offset tracking error",
                            lemma.char_offset, s.chars().count()
                        );
                        match s.chars().nth(lemma.char_offset) {
                            Some(ch) => self.ctx.terms.mk_string(ch.to_string()),
                            None => {
                                // Invalid offset into constant y: degrade to EmptySplit.
                                let empty = self.ctx.terms.mk_string(String::new());
                                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                                let neq = self.ctx.terms.mk_not(eq);
                                return vec![vec![eq, neq]];
                            }
                        }
                    }
                    _ => {
                        // Fallback: y is not a string constant or is empty.
                        // Degrade to EmptySplit.
                        let empty = self.ctx.terms.mk_string(String::new());
                        let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                        let neq = self.ctx.terms.mk_not(eq);
                        return vec![vec![eq, neq]];
                    }
                };

                // Build guard: x = "" (escape literal for empty-x branch)
                let empty = self.ctx.terms.mk_string(String::new());
                let x_eq_empty = self.ctx.terms.mk_eq(lemma.x, empty);

                // Get or create skolem for the remainder after first char.
                let k = skolem_cache.const_split(
                    &mut self.ctx.terms,
                    lemma.x,
                    lemma.y,
                    lemma.char_offset,
                );

                // Build: str.++(firstChar, k)
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![first_char, k],
                    Sort::String,
                );
                // Primary clause: x = "" OR x = str.++(firstChar, k)
                let eq = self.ctx.terms.mk_eq(lemma.x, concat);

                // Bridge axioms for skolem k (CVC5 lengthPositive pattern):
                // len(k) >= 0, len(k)=0 => k="", k="" => len(k)=0
                let mut aux = self.emit_skolem_len_bridge(k);

                // Concat length decomposition: len(str.++(c, k)) = 1 + len(k)
                let len_concat =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![concat], Sort::Int);
                let one = self.ctx.terms.mk_int(BigInt::from(1));
                let len_k_for_sum =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![k], Sort::Int);
                let sum = self.ctx.terms.mk_add(vec![one, len_k_for_sum]);
                let concat_len_eq = self.ctx.terms.mk_eq(len_concat, sum);
                aux.push(vec![concat_len_eq]);

                // Build the primary clause with NF reason guards (#4094).
                //
                // ConstSplit is context-dependent: it asserts that x starts
                // with a specific character derived from the NF comparison.
                // Without guards, stale ConstSplit clauses from backtracked
                // branches persist and force variables to wrong characters.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ ¬(reason_n) ∨ x="" ∨ x=char++k
                //
                // When the DPLL backtracks and undoes a reason literal, the
                // guard becomes true and the clause is trivially satisfied.
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                primary.push(x_eq_empty);
                primary.push(eq);

                let mut clauses = vec![primary];
                clauses.extend(aux);
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::ContainsPositive => {
                // Positive str.contains(x, y) reduction:
                //   x = sk_pre ++ y ++ sk_post
                // where sk_pre and sk_post are fresh skolem variables.
                //
                // This is a unit clause (always asserted): the CEGAR loop emits
                // this after the theory reported str.contains(x,y) = true with
                // non-ground arguments.
                //
                // Reference: CVC5 extf_solver.cpp:181-202

                // Get or create skolems for prefix and suffix.
                let sk_pre = skolem_cache.contains_pre(&mut self.ctx.terms, lemma.x, lemma.y);
                let sk_post = skolem_cache.contains_post(&mut self.ctx.terms, lemma.x, lemma.y);

                // Build: str.++(sk_pre, y, sk_post)
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, lemma.y, sk_post],
                    Sort::String,
                );

                // Primary clause: x = str.++(sk_pre, y, sk_post)
                let eq = self.ctx.terms.mk_eq(lemma.x, concat);

                // Bridge axioms for both skolems (CVC5 lengthPositive pattern)
                let mut clauses = vec![vec![eq]];
                clauses.extend(self.emit_skolem_len_bridge(sk_pre));
                clauses.extend(self.emit_skolem_len_bridge(sk_post));
                clauses
            }
            StringLemmaKind::SubstrReduction => {
                // On-demand substr reduction: lower the same axiom emitted by
                // preregistration, but only for the specific blocking term.
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if name != "str.substr" || args.len() != 3 {
                    return Vec::new();
                }
                let s = args[0];
                let n = args[1];
                let m = args[2];

                let sk_pre = skolem_cache.substr_pre(&mut self.ctx.terms, lemma.x);
                let skt = skolem_cache.substr_result(&mut self.ctx.terms, lemma.x);
                let sk_suf = skolem_cache.substr_suffix(&mut self.ctx.terms, lemma.x);

                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                let len_s = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
                let c1 = self.ctx.terms.mk_ge(n, zero);
                let c2 = self.ctx.terms.mk_gt(len_s, n);
                let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
                let c3 = self.ctx.terms.mk_gt(m, zero2);
                let cond = self.ctx.terms.mk_and(vec![c1, c2, c3]);

                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![sk_pre, skt, sk_suf],
                    Sort::String,
                );
                let b11 = self.ctx.terms.mk_eq(s, concat);

                let len_sk_pre =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![sk_pre], Sort::Int);
                let b12 = self.ctx.terms.mk_eq(len_sk_pre, n);

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

                let len_skt = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
                let b14 = self.ctx.terms.mk_le(len_skt, m);

                let then_branch = self.ctx.terms.mk_and(vec![b11, b12, b13, b14]);
                let empty = self.ctx.terms.mk_string(String::new());
                let else_branch = self.ctx.terms.mk_eq(skt, empty);
                let ite = self.ctx.terms.mk_ite(cond, then_branch, else_branch);
                let bridge = self.ctx.terms.mk_eq(lemma.x, skt);

                let mut clauses = Vec::new();
                clauses.extend(self.lower_dynamic_axiom_to_clauses(ite));
                clauses.extend(self.lower_dynamic_axiom_to_clauses(bridge));
                clauses.extend(self.emit_skolem_len_bridge(sk_pre));
                clauses.extend(self.emit_skolem_len_bridge(skt));
                clauses.extend(self.emit_skolem_len_bridge(sk_suf));
                clauses
            }
            StringLemmaKind::IndexofReduction => {
                // On-demand str.indexof(s, w, n) reduction (CAP-2).
                //
                // cvc5-style first-occurrence axiom (theory_strings_preprocess.cpp,
                // INDEXOF case). Let t be the indexof application itself (Int
                // sorted — used directly in the arithmetic atoms), and let
                // st = substr(s, n, len(s) - n) be the search window:
                //
                //   ite((n >= 0) and (n <= len(s)),
                //       ite(w = "",
                //           t = n,
                //           ite(contains(st, w),
                //               and(st = io_pre ++ w ++ io_suf,
                //                   t = n + len(io_pre),
                //                   not(contains(io_pre ++ w[0..|w|-1], w))),
                //               t = -1)),
                //       t = -1)
                //
                // Soundness (never excludes a real model): whenever the branch
                // conditions hold in a real model, the branch conclusion is
                // satisfiable by choosing io_pre = s[n..r] and io_suf = rest
                // where r = indexof(s, w, n): then t = n + len(io_pre) = r and
                // the leftmost guard holds because an occurrence of w inside
                // io_pre ++ w[0..|w|-1] would be an occurrence of w in s
                // starting in [n, r), contradicting r being the FIRST match at
                // or after n. io_pre/io_suf are fresh per indexof term, so the
                // conjunction is a pure skolemized definition.
                let Some(parts) = self.indexof_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let t = lemma.x;
                let w = parts.w;
                let n = parts.n;
                let len_s = parts.len_s;

                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
                let t_eq_neg1 = self.ctx.terms.mk_eq(t, neg_one);
                let t_eq_n = self.ctx.terms.mk_eq(t, n);

                // Valid-offset guard: n >= 0 and n <= len(s).
                let c1 = self.ctx.terms.mk_ge(n, zero);
                let c2 = self.ctx.terms.mk_le(n, len_s);
                let cond_valid = self.ctx.terms.mk_and(vec![c1, c2]);

                // Global range axiom (valid for every model): indexof >= -1.
                let t_ge_neg1 = self.ctx.terms.mk_ge(t, neg_one);

                // Empty constant needle: indexof(s, "", n) = n when the offset
                // is valid, -1 otherwise. No skolems needed.
                let (Some((io_pre, io_suf)), Some((contains_atom, leftmost_ctn))) =
                    (parts.skolems, parts.guards)
                else {
                    let top = self.ctx.terms.mk_ite(cond_valid, t_eq_n, t_eq_neg1);
                    let mut clauses = self.lower_dynamic_axiom_to_clauses(top);
                    clauses.push(vec![t_ge_neg1]);
                    return clauses;
                };

                // Found branch: window = io_pre ++ w ++ io_suf,
                // t = n + len(io_pre), and the leftmost guard.
                let concat = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![io_pre, w, io_suf],
                    Sort::String,
                );
                let window_eq = self.ctx.terms.mk_eq(parts.window, concat);

                let len_io_pre =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![io_pre], Sort::Int);
                let n_plus_pre = self.ctx.terms.mk_add(vec![n, len_io_pre]);
                let t_eq_pos = self.ctx.terms.mk_eq(t, n_plus_pre);

                // Leftmost guard: no occurrence of w may start before the
                // match, i.e. w does not occur in io_pre ++ w[0..|w|-1].
                let leftmost = self.ctx.terms.mk_not(leftmost_ctn);

                let found_branch = self.ctx.terms.mk_and(vec![window_eq, t_eq_pos, leftmost]);

                let inner2 = self
                    .ctx
                    .terms
                    .mk_ite(contains_atom, found_branch, t_eq_neg1);

                // Symbolic needle: peel the w = "" case (result is the offset).
                let inner1 = if parts.const_w.is_some() {
                    // Constant non-empty needle (empty handled above).
                    inner2
                } else {
                    let empty = self.ctx.terms.mk_string(String::new());
                    let w_empty = self.ctx.terms.mk_eq(w, empty);
                    self.ctx.terms.mk_ite(w_empty, t_eq_n, inner2)
                };

                let top = self.ctx.terms.mk_ite(cond_valid, inner1, t_eq_neg1);

                let mut clauses = Vec::new();
                clauses.extend(self.lower_dynamic_axiom_to_clauses(top));
                clauses.push(vec![t_ge_neg1]);
                clauses.extend(self.emit_skolem_len_bridge(io_pre));
                clauses.extend(self.emit_skolem_len_bridge(io_suf));
                clauses
            }
            StringLemmaKind::ReplaceReduction => {
                // On-demand str.replace(s, t, u) reduction (CAP-2 follow-on):
                //
                //   ite(t = "",
                //       r = u ++ s,
                //       ite(contains(s, t),
                //           and(s = rp_pre ++ t ++ rp_suf,
                //               not(contains(rp_pre ++ t[0..|t|-1], t)),
                //               r = rp_pre ++ u ++ rp_suf),
                //           r = s))
                //
                // where r is the replace application itself. Soundness (never
                // excludes a real model): with contains(s, t) true, choose
                // rp_pre/rp_suf around the FIRST occurrence of t — every
                // conjunct (including the leftmost guard) then holds and
                // r = rp_pre ++ u ++ rp_suf is exactly SMT-LIB str.replace.
                // The skolems are fresh per replace term, so the conjunction
                // is a pure skolemized definition.
                let Some(parts) = self.replace_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let r = lemma.x;
                let s = parts.s;
                let t = parts.t;
                let u = parts.u;

                // Empty constant needle: replace(s, "", u) = u ++ s.
                let (Some((rp_pre, rp_suf)), Some((contains_atom, leftmost_ctn))) =
                    (parts.skolems, parts.guards)
                else {
                    let us =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.++"), vec![u, s], Sort::String);
                    let eq = self.ctx.terms.mk_eq(r, us);
                    return vec![vec![eq]];
                };

                let concat_st = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![rp_pre, t, rp_suf],
                    Sort::String,
                );
                let s_eq = self.ctx.terms.mk_eq(s, concat_st);
                let concat_res = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![rp_pre, u, rp_suf],
                    Sort::String,
                );
                let r_eq = self.ctx.terms.mk_eq(r, concat_res);
                let leftmost = self.ctx.terms.mk_not(leftmost_ctn);
                let found_branch = self.ctx.terms.mk_and(vec![s_eq, r_eq, leftmost]);

                let r_eq_s = self.ctx.terms.mk_eq(r, s);
                let inner = self.ctx.terms.mk_ite(contains_atom, found_branch, r_eq_s);

                // Symbolic needle: peel the t = "" case (result is u ++ s).
                let top = if parts.const_t.is_some() {
                    // Constant non-empty needle (empty handled above).
                    inner
                } else {
                    let empty = self.ctx.terms.mk_string(String::new());
                    let t_empty = self.ctx.terms.mk_eq(t, empty);
                    let us =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("str.++"), vec![u, s], Sort::String);
                    let r_eq_us = self.ctx.terms.mk_eq(r, us);
                    self.ctx.terms.mk_ite(t_empty, r_eq_us, inner)
                };

                let mut clauses = Vec::new();
                clauses.extend(self.lower_dynamic_axiom_to_clauses(top));
                clauses.extend(self.emit_skolem_len_bridge(rp_pre));
                clauses.extend(self.emit_skolem_len_bridge(rp_suf));
                clauses
            }
            StringLemmaKind::ReplaceAllReduction => {
                // On-demand str.replace_all(s, t, u) ONE-STEP reduction
                // (extf wave 2):
                //
                //   ite(t = "",
                //       r = s,                       // UNCHANGED (≠ replace!)
                //       ite(contains(s, t),
                //           and(s = rpa_pre ++ t ++ rpa_suf,
                //               not(contains(rpa_pre ++ t[0..|t|-1], t)),
                //               r = rpa_pre ++ u ++ replace_all(rpa_suf, t, u)),
                //           r = s))
                //
                // where r is the replace_all application itself and the
                // recursive application is reduced on demand in later CEGAR
                // rounds (budget-bounded by the string core; past the budget
                // it stays unreduced and the solver reports Unknown).
                //
                // Soundness (never excludes a real model): with
                // contains(s, t) true and t non-empty, choose rpa_pre/rpa_suf
                // around the FIRST occurrence of t — every conjunct holds and
                // SMT-LIB replace_all is exactly "replace the first match,
                // then replace_all the remaining suffix". The skolems are
                // fresh per application, so the conjunction is a pure
                // skolemized definition; the recursive application keeps
                // exact SMT-LIB semantics (enforced by later reductions,
                // ground evaluation, and the final model-validation
                // chokepoint).
                let Some(parts) = self.replace_all_reduction_parts(lemma.x, skolem_cache) else {
                    return Vec::new();
                };
                let r = lemma.x;
                let s = parts.s;
                let t = parts.t;
                let u = parts.u;

                let r_eq_s = self.ctx.terms.mk_eq(r, s);

                // Empty constant needle: replace_all(s, "", u) = s.
                let (Some((rpa_pre, rpa_suf, rest)), Some((contains_atom, leftmost_ctn))) =
                    (parts.skolems, parts.guards)
                else {
                    return vec![vec![r_eq_s]];
                };

                let concat_st = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![rpa_pre, t, rpa_suf],
                    Sort::String,
                );
                let s_eq = self.ctx.terms.mk_eq(s, concat_st);
                let concat_res = self.ctx.terms.mk_app(
                    Symbol::named("str.++"),
                    vec![rpa_pre, u, rest],
                    Sort::String,
                );
                let r_eq = self.ctx.terms.mk_eq(r, concat_res);
                let leftmost = self.ctx.terms.mk_not(leftmost_ctn);

                // Explicit branch-local length equations (implied by the two
                // concat equalities, so adding them as conjuncts keeps the
                // branch valid). These are what bound the recursion: with
                // len(r) pinned and len(u) known, each unroll step forces
                // len(rest) <= len(r) - len(u), so the LIA solver refutes a
                // contains-branch dive past len(r)/max(len(u),1) steps and
                // the SAT solver flips to the no-match base case instead of
                // consuming the whole unroll budget.
                let len_s = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
                let len_pre =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![rpa_pre], Sort::Int);
                let len_t = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![t], Sort::Int);
                let len_suf =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![rpa_suf], Sort::Int);
                let s_len_sum = self.ctx.terms.mk_add(vec![len_pre, len_t, len_suf]);
                let s_len_eq = self.ctx.terms.mk_eq(len_s, s_len_sum);
                let len_r = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![r], Sort::Int);
                let len_u = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![u], Sort::Int);
                let len_rest =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![rest], Sort::Int);
                let r_len_sum = self.ctx.terms.mk_add(vec![len_pre, len_u, len_rest]);
                let r_len_eq = self.ctx.terms.mk_eq(len_r, r_len_sum);

                let found_branch = self
                    .ctx
                    .terms
                    .mk_and(vec![s_eq, r_eq, leftmost, s_len_eq, r_len_eq]);

                let inner = self.ctx.terms.mk_ite(contains_atom, found_branch, r_eq_s);

                // Symbolic needle: peel the t = "" case (result is s).
                let top = if parts.const_t.is_some() {
                    // Constant non-empty needle (empty handled above).
                    inner
                } else {
                    let empty = self.ctx.terms.mk_string(String::new());
                    let t_empty = self.ctx.terms.mk_eq(t, empty);
                    self.ctx.terms.mk_ite(t_empty, r_eq_s, inner)
                };

                let mut clauses = Vec::new();
                clauses.extend(self.lower_dynamic_axiom_to_clauses(top));
                clauses.extend(self.emit_skolem_len_bridge(rpa_pre));
                clauses.extend(self.emit_skolem_len_bridge(rpa_suf));
                clauses
            }
            StringLemmaKind::ToIntReduction => {
                self.create_to_int_reduction_clauses(lemma, skolem_cache)
            }
            StringLemmaKind::ReplaceReReduction | StringLemmaKind::ReplaceReAllReduction => {
                // Partial regex-replace reduction (extf wave 2 Part B), for
                // GROUND engine-evaluable regexes only (the string core
                // checks this before requesting):
                //
                //   (str.in_re s (re.++ re.all R re.all)) ∨ (r = s)
                //
                // "No match anywhere in s → the result is s unchanged" —
                // valid for both str.replace_re (first match) and
                // str.replace_re_all (all matches). The exact match
                // semantics are enforced by ground evaluation once `s`
                // resolves (the regex engine computes leftmost-shortest
                // matches; replace_re_all replaces only NON-EMPTY matches)
                // together with the definitive model-validation chokepoint.
                // An unresolved membership keeps the regexp solver's
                // incompleteness latch, so Unknown stays honest; UNSAT
                // conclusions only ever use the valid clause above.
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if !(name == "str.replace_re" || name == "str.replace_re_all") || args.len() != 3 {
                    return Vec::new();
                }
                let r = lemma.x;
                let s = args[0];
                let re = args[1];

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
                let r_eq_s = self.ctx.terms.mk_eq(r, s);

                // Result skolem bridge (mirrors the substr reduction): give
                // the application's EQC a plain string VARIABLE so the
                // normal form machinery does not bail (Incomplete) on an
                // opaque extf application component.
                let rsk = skolem_cache.replace_result(&mut self.ctx.terms, r);
                let bridge = self.ctx.terms.mk_eq(r, rsk);

                let mut clauses = vec![vec![match_atom, r_eq_s], vec![bridge]];
                clauses.extend(self.emit_skolem_len_bridge(rsk));
                clauses
            }
            StringLemmaKind::FromIntReduction => {
                // On-demand str.from_int(n) reduction (extf wave 2), via the
                // mutual to_int definition plus a canonical-decimal regex:
                //
                //   ite(n >= 0,
                //       and(to_int(r) = n,
                //           r ∈ ("0" | [1-9][0-9]*)),
                //       r = "")
                //
                // where r is the from_int application itself. Soundness:
                // for n >= 0, SMT-LIB from_int(n) is the unique all-digit
                // string without leading zeros whose to_int value is n —
                // exactly the conjunction above; for n < 0 the result is "".
                // The inner to_int(r) application stays unreduced unless a
                // later round can reduce/evaluate it, in which case the
                // solver honestly reports Unknown rather than guessing.
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
                    return Vec::new();
                };
                if !(name == "str.from_int" || name == "int.to.str") || args.len() != 1 {
                    return Vec::new();
                }
                let r = lemma.x;
                let n = args[0];

                let to_int = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("str.to_int"), vec![r], Sort::Int);
                let to_int_eq_n = self.ctx.terms.mk_eq(to_int, n);

                // Canonical decimal regex: (re.union (str.to_re "0")
                //   (re.++ (re.range "1" "9") (re.* (re.range "0" "9")))).
                let zero_str = self.ctx.terms.mk_string("0".to_string());
                let re_zero =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.to_re"), vec![zero_str], Sort::RegLan);
                let one_str = self.ctx.terms.mk_string("1".to_string());
                let nine_str = self.ctx.terms.mk_string("9".to_string());
                let re_1_9 = self.ctx.terms.mk_app(
                    Symbol::named("re.range"),
                    vec![one_str, nine_str],
                    Sort::RegLan,
                );
                let zero_str2 = self.ctx.terms.mk_string("0".to_string());
                let nine_str2 = self.ctx.terms.mk_string("9".to_string());
                let re_0_9 = self.ctx.terms.mk_app(
                    Symbol::named("re.range"),
                    vec![zero_str2, nine_str2],
                    Sort::RegLan,
                );
                let re_0_9_star =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("re.*"), vec![re_0_9], Sort::RegLan);
                let re_pos = self.ctx.terms.mk_app(
                    Symbol::named("re.++"),
                    vec![re_1_9, re_0_9_star],
                    Sort::RegLan,
                );
                let re_canonical = self.ctx.terms.mk_app(
                    Symbol::named("re.union"),
                    vec![re_zero, re_pos],
                    Sort::RegLan,
                );
                let membership = self.ctx.terms.mk_app(
                    Symbol::named("str.in_re"),
                    vec![r, re_canonical],
                    Sort::Bool,
                );

                let zero = self.ctx.terms.mk_int(BigInt::from(0));
                let n_ge_0 = self.ctx.terms.mk_ge(n, zero);
                let then_branch = self.ctx.terms.mk_and(vec![to_int_eq_n, membership]);
                let empty = self.ctx.terms.mk_string(String::new());
                let r_eq_empty = self.ctx.terms.mk_eq(r, empty);
                let top = self.ctx.terms.mk_ite(n_ge_0, then_branch, r_eq_empty);

                let mut clauses = self.lower_dynamic_axiom_to_clauses(top);

                // Ground-inversion instances (extf wave 2): when an
                // assertion compares this from_int application against a
                // string LITERAL c, emit the corresponding universally valid
                // from_int axiom instance so the integer argument is linked
                // arithmetically (the strings core can evaluate to_int of a
                // resolved constant but has no channel to propagate the
                // integer value into LIA):
                // - canonical decimal c: (r = c) → (n = value(c));
                // - c = "":            (r = "") → (n <= -1);
                // - non-canonical c:   ¬(r = c)   (from_int never yields it).
                clauses.extend(self.from_int_ground_inversion_clauses(r, n));
                clauses
            }
            StringLemmaKind::ConstUnify => {
                // Length-aware constant unification (#4055): x = prefix(y, n).
                //
                // When a variable x has known length n and is compared against
                // a constant y with len(y) >= n, directly assert x = y[0..n].
                // The char_offset field carries n (the prefix length).
                //
                // This resolves in one CEGAR step what ConstSplit would need
                // n character-by-character iterations to accomplish.
                //
                // The variable unifies with the substring `y[start..end]` where
                // `start = lemma.start_offset` and `end = lemma.char_offset`.
                // In the simple (prefix) case start is 0; in the partial-offset
                // case a preceding concat component already consumed `start`
                // characters of `y`, so the variable equals the *substring*, not
                // the prefix `y[0..end]` (which was the cause of false-unknown on
                // satisfiable concat+length instances).
                let prefix_str = match self.ctx.terms.get(lemma.y) {
                    TermData::Const(Constant::String(s)) => {
                        let chars: Vec<char> = s.chars().collect();
                        debug_assert!(
                            lemma.char_offset <= chars.len(),
                            "BUG: ConstUnify char_offset {} > constant y length {} — substring silently truncated",
                            lemma.char_offset, chars.len()
                        );
                        debug_assert!(
                            lemma.start_offset <= lemma.char_offset,
                            "BUG: ConstUnify start_offset {} > char_offset {} — inverted substring range",
                            lemma.start_offset, lemma.char_offset
                        );
                        let end = lemma.char_offset.min(chars.len());
                        let start = lemma.start_offset.min(end);
                        chars[start..end].iter().collect::<String>()
                    }
                    _ => {
                        // y is not a string constant — degrade to EmptySplit.
                        let empty = self.ctx.terms.mk_string(String::new());
                        let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                        let neq = self.ctx.terms.mk_not(eq);
                        return vec![vec![eq, neq]];
                    }
                };
                let prefix_term = self.ctx.terms.mk_string(prefix_str);
                let eq = self.ctx.terms.mk_eq(lemma.x, prefix_term);

                // Guard the equality clause with NF context reasons (#6273).
                // ConstUnify is context-dependent like ConstSplit: it asserts
                // x = prefix(y, n) based on the NF alignment. Without guards,
                // stale ConstUnify clauses persist after DPLL backtracking and
                // force wrong equalities, causing false-UNSAT.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ ¬(reason_n) ∨ x=prefix(y,n)
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 1);
                primary.push(eq);

                // Length axiom for the substring constant (tautology, no guards
                // needed). The substring spans `[start_offset, char_offset)`, so
                // its length is `char_offset - start_offset` (not `char_offset`).
                let len_prefix =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![prefix_term], Sort::Int);
                let sub_len = lemma.char_offset.saturating_sub(lemma.start_offset);
                let n_val = self.ctx.terms.mk_int(BigInt::from(sub_len));
                let len_eq = self.ctx.terms.mk_eq(len_prefix, n_val);

                let mut clauses = vec![primary, vec![len_eq]];
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::VarSplit => {
                // SSPLIT_VAR: len(x)=len(y) OR (x = y ++ k) OR (y = x ++ k).
                //
                // Guard: VarSplit is only valid under len(x) != len(y). To
                // prevent over-constraining the equal-length branch, we add
                // `len(x) = len(y)` as an escape literal in the primary clause.
                // When SAT backtracks to len(x) = len(y), the clause is trivially
                // satisfied via the guard, and the split skolem k is unconstrained.
                //
                // CVC5 reference: core_solver.cpp:1642 asserts areDisequal(lenx, leny).
                // CVC5 uses explanation-guarded lemmas; AY achieves the same effect
                // by including the negated precondition in the clause itself (#3375).

                // Get or create skolem for the split remainder.
                let k = skolem_cache.var_split(&mut self.ctx.terms, lemma.x, lemma.y);

                // Build guard: len(x) = len(y) (escape literal for equal-length branch)
                let len_x =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.x], Sort::Int);
                let len_y =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), vec![lemma.y], Sort::Int);
                let len_eq = self.ctx.terms.mk_eq(len_x, len_y);

                // Build: str.++(y, k) and str.++(x, k)
                let concat_yk =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.++"), vec![lemma.y, k], Sort::String);
                let concat_xk =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.++"), vec![lemma.x, k], Sort::String);

                // Primary clause: len(x)=len(y) OR x=str.++(y,k) OR y=str.++(x,k)
                let eq_xy = self.ctx.terms.mk_eq(lemma.x, concat_yk);
                let eq_yx = self.ctx.terms.mk_eq(lemma.y, concat_xk);

                // Build the primary clause with NF reason guards (#4094).
                //
                // VarSplit is context-dependent: it asserts that one of x,y
                // is a prefix of the other, which depends on the NF comparison
                // context. Without guards, stale VarSplit clauses persist after
                // DPLL backtracking and over-constrain variables.
                //
                // Non-emptiness guards (#6273): CVC5 adds explainNonEmpty(nc) to
                // VarSplit premises (core_solver.cpp:1702-1716). Without these,
                // the VarSplit clause is active even when a component is empty,
                // creating contradictions with ConstSplit clauses from the empty
                // branch. We add (x="") and (y="") as positive escape literals:
                // when a component IS empty, the escape literal is true and the
                // clause is trivially satisfied; when non-empty, the escape
                // literal is false and the VarSplit disjuncts remain active.
                //
                // Clause: ¬(reason_1) ∨ ... ∨ x="" ∨ y="" ∨ len(x)=len(y) ∨ x=y++k ∨ y=x++k
                let empty = self.ctx.terms.mk_string(String::new());
                let x_empty = self.ctx.terms.mk_eq(lemma.x, empty);
                let y_empty = self.ctx.terms.mk_eq(lemma.y, empty);
                let mut primary = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 5);
                primary.push(x_empty);
                primary.push(y_empty);
                primary.push(len_eq);
                primary.push(eq_xy);
                primary.push(eq_yx);

                // Bridge axioms for skolem k (CVC5 lengthPositive pattern)
                let mut clauses = vec![primary];
                clauses.extend(self.emit_skolem_len_bridge(k));
                // Emit companion EmptySplit clauses for guard variables (#6273).
                clauses.extend(emit_guard_empty_splits(&mut self.ctx.terms, &lemma.reason));
                clauses
            }
            StringLemmaKind::EqualitySplit => {
                // DEQ_STRINGS_EQ: x = y OR x != y.
                //
                // Emitted by process_simple_deq when two NF components have
                // equal lengths but unknown equality status. Forces the SAT
                // solver to decide: if x = y, the disequality may still hold
                // via other NF components; if x != y, the disequality is
                // directly satisfied at this position.
                //
                // CVC5 reference: core_solver.cpp:2280-2300 (sendSplit on
                // mismatched components after processSimpleDeq returns false).
                let eq = self.ctx.terms.mk_eq(lemma.x, lemma.y);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            StringLemmaKind::DeqEmptySplit => {
                // DEQ_DISL_EMP_SPLIT: x = "" OR x != "".
                //
                // One NF component is constant, the other (x) is non-constant
                // and may be empty. Forces the SAT solver to decide emptiness
                // before the caller can apply decomposition cases.
                //
                // CVC5 reference: core_solver.cpp:2157-2167.
                let empty = self.ctx.terms.mk_string(String::new());
                let eq = self.ctx.terms.mk_eq(lemma.x, empty);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            StringLemmaKind::DeqFirstCharEqSplit => {
                // DEQ_DISL_FIRST_CHAR_EQ_SPLIT: x = c OR x != c.
                //
                // Non-constant x has length 1; lemma.y is the constant
                // component. Extract the first character and split on
                // equality with it.
                //
                // CVC5 reference: core_solver.cpp:2192-2198.
                let first_char_term =
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(lemma.y) {
                        let ch: String = s.chars().take(1).collect();
                        self.ctx.terms.mk_string(ch)
                    } else {
                        // Fallback: use the full constant term.
                        lemma.y
                    };
                let eq = self.ctx.terms.mk_eq(lemma.x, first_char_term);
                let neq = self.ctx.terms.mk_not(eq);
                let mut clause = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
                clause.push(eq);
                clause.push(neq);
                vec![clause]
            }
            _ => {
                // Future StringLemmaKind variants — return empty for now.
                vec![]
            }
        }
    }

    /// Universally valid `str.from_int` inversion instances for string
    /// literals the application is compared against in the assertion set
    /// (extf wave 2).
    ///
    /// For each asserted-shape equality `(= r c)` / `(= c r)` with a string
    /// literal `c` (scanned through top-level `not`/`or`/`and` structure):
    /// - `c` canonical (`"0"` or `[1-9][0-9]*`): `(r = c) → (n = value(c))`;
    /// - `c = ""`: `(r = "") → (n <= -1)` (from_int of a negative is `""`);
    /// - otherwise (leading zero / non-digit): `¬(r = c)` — `str.from_int`
    ///   never produces a non-canonical string.
    ///
    /// Every clause is an instance of the SMT-LIB from_int axiom, valid in
    /// every model regardless of where the equality atom occurs, so no
    /// guards are needed.
    // Named after the SMT-LIB `str.from_int` operator, not a `from_*` constructor.
    #[allow(clippy::wrong_self_convention)]
    fn from_int_ground_inversion_clauses(&mut self, r: TermId, n: TermId) -> Vec<Vec<TermId>> {
        // Collect candidate literals first (immutable scan), then build terms.
        let mut literals: Vec<String> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: Vec<TermId> = Vec::new();
        while let Some(t) = stack.pop() {
            if seen.contains(&t) {
                continue;
            }
            seen.push(t);
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push(*inner),
                TermData::App(Symbol::Named(name), args) => {
                    if (name == "or" || name == "and") && !args.is_empty() {
                        stack.extend(args.iter().copied());
                    } else if name == "=" && args.len() == 2 {
                        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                            if lhs == r {
                                if let TermData::Const(Constant::String(c)) =
                                    self.ctx.terms.get(rhs)
                                {
                                    if !literals.contains(c) {
                                        literals.push(c.clone());
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        let mut clauses = Vec::new();
        for c in literals {
            let c_term = self.ctx.terms.mk_string(c.clone());
            let r_eq_c = self.ctx.terms.mk_eq(r, c_term);
            let not_r_eq_c = self.ctx.terms.mk_not(r_eq_c);
            if c.is_empty() {
                // (r = "") → (n <= -1).
                let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
                let n_le_neg1 = self.ctx.terms.mk_le(n, neg_one);
                clauses.push(vec![not_r_eq_c, n_le_neg1]);
            } else if c.chars().all(|ch| ch.is_ascii_digit())
                && (c.len() == 1 || !c.starts_with('0'))
            {
                // Canonical decimal: (r = c) → (n = value(c)).
                let Ok(value) = c.parse::<BigInt>() else {
                    continue;
                };
                let value_term = self.ctx.terms.mk_int(value);
                let n_eq_value = self.ctx.terms.mk_eq(n, value_term);
                clauses.push(vec![not_r_eq_c, n_eq_value]);
            } else {
                // Non-canonical: from_int never produces it.
                clauses.push(vec![not_r_eq_c]);
            }
        }
        clauses
    }

    /// On-demand `str.to_int(s)` reduction via digit decomposition
    /// (extf wave 2).
    ///
    /// `lemma.char_offset` carries a concrete upper bound `L` on `len(s)`
    /// derived from the asserted literal in `lemma.reason`; every
    /// case clause is guarded by that literal's negation (mirroring
    /// ConstSplit's context guards), so backtracking the bound deactivates
    /// the encoding. Let `t` be the to_int application itself (Int sorted):
    ///
    /// - `t >= -1` (universal range axiom);
    /// - guarded coverage: `len(s) = 0 ∨ ... ∨ len(s) = L`;
    /// - `len(s) = 0 → t = -1` (to_int("") = -1);
    /// - for `k` in `1..=L`: `len(s) = k →`
    ///   `s = d_1 ++ ... ++ d_k ∧ ite(∧ v_i >= 0, t = Σ 10^(k-i)·v_i, t = -1)`
    ///   where `d_i` are shared single-char position skolems and `v_i` their
    ///   digit values (`-1` for non-digits, else `0..=9`, linked by
    ///   `d_i = "c" → v_i = c` implications plus a coverage clause).
    ///
    /// Soundness (never excludes a real model): every string of length `k`
    /// decomposes into `k` single chars witnessing the skolems; when all
    /// chars are digits, SMT-LIB `to_int` is exactly the decimal sum with
    /// leading zeros contributing 0 to their weight; otherwise (or for the
    /// empty string) it is `-1`. Guarded clauses are valid implications of
    /// the reason literal, so UNSAT conclusions remain sound; SAT models are
    /// re-validated by the definitive-eval chokepoint regardless.
    fn create_to_int_reduction_clauses(
        &mut self,
        lemma: &StringLemma,
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Vec<Vec<TermId>> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(lemma.x) else {
            return Vec::new();
        };
        if !(name == "str.to_int" || name == "str.to.int") || args.len() != 1 {
            return Vec::new();
        }
        let s = args[0];
        let t = lemma.x;
        let bound = lemma.char_offset;

        let len_s = self
            .ctx
            .terms
            .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
        let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
        let t_eq_neg1 = self.ctx.terms.mk_eq(t, neg_one);
        let t_ge_neg1 = self.ctx.terms.mk_ge(t, neg_one);

        // Universal range axiom (valid in every model): to_int >= -1.
        let mut clauses = vec![vec![t_ge_neg1]];

        // len(s) = k atoms for k in 0..=L.
        let len_eq_atoms: Vec<TermId> = (0..=bound)
            .map(|k| {
                let k_term = self.ctx.terms.mk_int(BigInt::from(k));
                self.ctx.terms.mk_eq(len_s, k_term)
            })
            .collect();

        // Guarded coverage: reason implies len(s) <= L, so one of the
        // length atoms must hold. Gives the SAT solver the propositional
        // case split directly instead of waiting for LIA to refute
        // "all length atoms false".
        let mut coverage = build_reason_guard(&mut self.ctx.terms, &lemma.reason, bound + 1);
        coverage.extend(len_eq_atoms.iter().copied());
        clauses.push(coverage);

        // k = 0: the empty string is not a digit string; to_int = -1.
        let not_len0 = self.ctx.terms.mk_not(len_eq_atoms[0]);
        let mut c0 = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
        c0.push(not_len0);
        c0.push(t_eq_neg1);
        clauses.push(c0);

        // Shared per-position digit skolems and their value links
        // (unguarded: valid definitions of otherwise-unconstrained fresh
        // skolems).
        let mut digits = Vec::with_capacity(bound);
        let mut values = Vec::with_capacity(bound);
        let zero = self.ctx.terms.mk_int(BigInt::from(0));
        let nine = self.ctx.terms.mk_int(BigInt::from(9));
        let one = self.ctx.terms.mk_int(BigInt::from(1));
        for i in 1..=bound {
            let d = skolem_cache.to_int_digit(&mut self.ctx.terms, lemma.x, i);
            let v = skolem_cache.to_int_digit_val(&mut self.ctx.terms, lemma.x, i);
            digits.push(d);
            values.push(v);

            // len(d_i) = 1: single-character position skolem.
            let len_d = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![d], Sort::Int);
            let len_d_eq_1 = self.ctx.terms.mk_eq(len_d, one);
            clauses.push(vec![len_d_eq_1]);

            // d_i = "c" → v_i = c for each digit c, plus the coverage
            // clause d_i ∈ {"0"..."9"} ∨ v_i = -1 (non-digit marker).
            let mut digit_coverage = Vec::with_capacity(11);
            for c in 0..=9u32 {
                let c_str = self.ctx.terms.mk_string(c.to_string());
                let d_eq_c = self.ctx.terms.mk_eq(d, c_str);
                let c_int = self.ctx.terms.mk_int(BigInt::from(c));
                let v_eq_c = self.ctx.terms.mk_eq(v, c_int);
                let not_d_eq_c = self.ctx.terms.mk_not(d_eq_c);
                clauses.push(vec![not_d_eq_c, v_eq_c]);
                digit_coverage.push(d_eq_c);
            }
            let v_eq_neg1 = self.ctx.terms.mk_eq(v, neg_one);
            digit_coverage.push(v_eq_neg1);
            clauses.push(digit_coverage);

            // -1 <= v_i <= 9.
            let v_ge_neg1 = self.ctx.terms.mk_ge(v, neg_one);
            let v_le_9 = self.ctx.terms.mk_le(v, nine);
            clauses.push(vec![v_ge_neg1]);
            clauses.push(vec![v_le_9]);
        }

        // Per-length cases k in 1..=L.
        for k in 1..=bound {
            let concat_eq = if k == 1 {
                self.ctx.terms.mk_eq(s, digits[0])
            } else {
                let concat =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.++"), &digits[..k], Sort::String);
                self.ctx.terms.mk_eq(s, concat)
            };

            // All-digit condition over the first k positions.
            let digit_conds: Vec<TermId> = values[..k]
                .iter()
                .map(|&v| self.ctx.terms.mk_ge(v, zero))
                .collect();
            let all_digits = self.ctx.terms.mk_and(digit_conds);

            // Decimal value: Σ 10^(k-i) · v_i (1-based i).
            let mut sum_terms = Vec::with_capacity(k);
            for (idx, &v) in values[..k].iter().enumerate() {
                let power = (k - 1 - idx) as u32;
                if power == 0 {
                    sum_terms.push(v);
                } else {
                    let coeff = BigInt::from(10u32).pow(power);
                    let coeff_term = self.ctx.terms.mk_int(coeff);
                    sum_terms.push(self.ctx.terms.mk_mul(vec![coeff_term, v]));
                }
            }
            let sum = if sum_terms.len() == 1 {
                sum_terms[0]
            } else {
                self.ctx.terms.mk_add(sum_terms)
            };
            let t_eq_sum = self.ctx.terms.mk_eq(t, sum);
            let value_link = self.ctx.terms.mk_ite(all_digits, t_eq_sum, t_eq_neg1);

            let case_k = self.ctx.terms.mk_and(vec![concat_eq, value_link]);
            let not_len_k = self.ctx.terms.mk_not(len_eq_atoms[k]);
            let mut ck = build_reason_guard(&mut self.ctx.terms, &lemma.reason, 2);
            ck.push(not_len_k);
            ck.push(case_k);
            clauses.push(ck);
        }

        debug_assert!(
            clauses.iter().all(|c| !c.is_empty()),
            "BUG: create_to_int_reduction_clauses produced empty clause — would cause false UNSAT"
        );
        clauses
    }

    /// Emit bridge axioms for a split skolem variable `k`.
    ///
    /// Returns clauses encoding the CVC5 `lengthPositive` pattern:
    /// 1. `len(k) >= 0` — non-negativity
    /// 2. `len(k) = 0 => k = ""` — zero-length implies empty
    /// 3. `k = "" => len(k) = 0` — empty implies zero-length
    ///
    /// These axioms close the gap between the SAT-level split lemma and
    /// the LIA length reasoning, allowing the CEGAR loop to converge on
    /// QF_SLIA problems involving split-generated skolems.
    ///
    /// Reference: CVC5 `term_registry.cpp:173-185` (`lengthPositive`).
    pub(in crate::executor) fn emit_skolem_len_bridge(&mut self, k: TermId) -> Vec<Vec<TermId>> {
        let len_k = self
            .ctx
            .terms
            .mk_app(Symbol::named("str.len"), vec![k], Sort::Int);
        let zero = self.ctx.terms.mk_int(BigInt::from(0));
        let empty = self.ctx.terms.mk_string(String::new());

        // Axiom 1: len(k) >= 0
        let len_ge_zero = self.ctx.terms.mk_ge(len_k, zero);

        // Axiom 2: len(k) = 0 => k = ""
        // Encoded as clause: [NOT(len(k)=0), k=""]
        // This ensures both atoms are separate theory atoms that the string
        // solver can process. The previous encoding as mk_implies created an
        // opaque atom invisible to the theory (#3429).
        let zero2 = self.ctx.terms.mk_int(BigInt::from(0));
        let len_eq_zero = self.ctx.terms.mk_eq(len_k, zero2);
        let k_eq_empty = self.ctx.terms.mk_eq(k, empty);
        let not_len_eq_zero = self.ctx.terms.mk_not(len_eq_zero);

        // Axiom 3: k = "" => len(k) = 0
        // Encoded as clause: [NOT(k=""), len(k)=0]
        let not_k_eq_empty = self.ctx.terms.mk_not(k_eq_empty);
        let zero3 = self.ctx.terms.mk_int(BigInt::from(0));
        let len_eq_zero2 = self.ctx.terms.mk_eq(len_k, zero3);

        let clauses = vec![
            vec![len_ge_zero],
            vec![not_len_eq_zero, k_eq_empty],
            vec![not_k_eq_empty, len_eq_zero2],
        ];
        debug_assert!(
            clauses.iter().all(|c| !c.is_empty()),
            "BUG: emit_skolem_len_bridge produced empty clause — would cause false UNSAT"
        );
        clauses
    }

    /// Dynamic axioms are injected as raw SAT clauses via `apply_string_lemma`.
    ///
    /// Unlike the initial preprocessed assertion set, this path does not run
    /// Tseitin transformation. Lower implication terms to CNF at insertion time
    /// so `(=> a b)` contributes as `(~a \/ b)` instead of an opaque atom.
    pub(in crate::executor) fn lower_dynamic_axiom_to_clauses(
        &mut self,
        axiom: TermId,
    ) -> Vec<Vec<TermId>> {
        match self.ctx.terms.get(axiom) {
            // Disjunction (or a b ...): treat as a single clause with each disjunct as a literal.
            // mk_implies(a, b) desugars to or(not(a), b), so this handles implications.
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
                vec![args.clone()]
            }
            // Conjunction (and a b ...): each conjunct becomes a separate unit clause.
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() >= 2 => {
                args.iter().map(|&a| vec![a]).collect()
            }
            // Atom or anything else: single unit clause.
            _ => vec![vec![axiom]],
        }
    }
}
