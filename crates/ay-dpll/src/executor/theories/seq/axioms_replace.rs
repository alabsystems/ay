// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replacement seq axiom generation: `seq.replace`.
//!
//! Extracted from `axioms_indexof.rs` as part of code-health module split (#5970).
//! Index-finding operations (indexof, last_indexof) remain in `axioms_indexof`.

use num_bigint::BigInt;
use num_traits::Zero;

use super::super::super::Executor;
use super::scan::SeqTermScan;
use ay_core::term::{Symbol, TermId};

impl Executor {
    /// Generate `seq.replace` axioms (#5841).
    ///
    /// For `r = seq.replace(u, src, dst)` — replace first occurrence of `src` in `u` with `dst`.
    ///
    /// Reference: Z3 seq_axioms.cpp:555-590 + tightest_prefix (373-390).
    ///
    /// Returns `(axioms, new_contains_terms)` where `new_contains_terms` are fresh
    /// `contains(u, src)` terms that need skolem decomposition.
    pub(super) fn generate_seq_replace_axioms(
        &mut self,
        scan: &SeqTermScan,
    ) -> (Vec<TermId>, Vec<(TermId, TermId, TermId)>) {
        let mut axioms = Vec::new();
        let mut new_contains_terms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let one = self.ctx.terms.mk_int(BigInt::from(1));

        for &(replace_term, u, src, dst) in &scan.replace_terms {
            let seq_sort = self.ctx.terms.sort(u).clone();

            let empty = self.mk_seq_empty(&seq_sort);
            let src_eq_empty = self.ctx.terms.mk_eq(src, empty);
            let u_eq_empty = self.ctx.terms.mk_eq(u, empty);

            // Create contains(u, src) — tracked for caller axiom generation.
            let contains = self.ctx.terms.mk_app(
                Symbol::named("seq.contains"),
                vec![u, src],
                ay_core::Sort::Bool,
            );
            new_contains_terms.push((contains, u, src));

            // Axiom 1: src = "" => r = dst ++ u
            // When the search pattern is empty, Z3 prepends dst to u.
            let dst_u =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![dst, u], seq_sort.clone());
            let r_eq_dst_u = self.ctx.terms.mk_eq(replace_term, dst_u);
            axioms.push(self.ctx.terms.mk_implies(src_eq_empty, r_eq_dst_u));

            // Axiom 2: u = "" => src = "" OR r = u
            // If haystack is empty and needle is non-empty, nothing to replace.
            let r_eq_u = self.ctx.terms.mk_eq(replace_term, u);
            let disj = self.ctx.terms.mk_or(vec![src_eq_empty, r_eq_u]);
            axioms.push(self.ctx.terms.mk_implies(u_eq_empty, disj));

            // Axiom 3: !contains(u, src) => r = u
            let not_contains = self.ctx.terms.mk_not(contains);
            let nc_r_eq_u = self.ctx.terms.mk_eq(replace_term, u);
            axioms.push(self.ctx.terms.mk_implies(not_contains, nc_r_eq_u));

            // Skolem witnesses for decomposition around first occurrence.
            // u = x ++ src ++ y, r = x ++ dst ++ y
            let sk_x = self.ctx.terms.mk_fresh_var("seq.rpl.x", seq_sort.clone());
            let sk_y = self.ctx.terms.mk_fresh_var("seq.rpl.y", seq_sort.clone());

            let src_ne_empty = self.ctx.terms.mk_not(src_eq_empty);
            let u_ne_empty = self.ctx.terms.mk_not(u_eq_empty);

            // Guard: contains(u, src) & u != "" & src != ""
            let guard = self
                .ctx
                .terms
                .mk_and(vec![contains, u_ne_empty, src_ne_empty]);

            // Axiom 4: guard => u = x ++ src ++ y
            let src_y =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![src, sk_y], seq_sort.clone());
            let x_src_y =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![sk_x, src_y], seq_sort.clone());
            let u_eq_decomp = self.ctx.terms.mk_eq(u, x_src_y);
            axioms.push(self.ctx.terms.mk_implies(guard, u_eq_decomp));

            // Axiom 5: guard => r = x ++ dst ++ y
            let dst_y =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![dst, sk_y], seq_sort.clone());
            let x_dst_y =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), vec![sk_x, dst_y], seq_sort.clone());
            let r_eq_replaced = self.ctx.terms.mk_eq(replace_term, x_dst_y);
            axioms.push(self.ctx.terms.mk_implies(guard, r_eq_replaced));

            // Tightest prefix: ensure x is the shortest prefix before
            // the first occurrence of src (leftmost match guarantee).
            // Z3 seq_axioms.cpp:373-390.
            //
            // src = "" OR !contains(x ++ extract(src, 0, len(src)-1), src)
            //
            // This says: x concatenated with src-minus-last-char does NOT
            // contain src, ensuring we found the leftmost occurrence.
            let len_src = self.mk_seq_len(src);
            let len_src_m1 = self.ctx.terms.mk_sub(vec![len_src, one]);
            let src_init = self.ctx.terms.mk_app(
                Symbol::named("seq.extract"),
                vec![src, zero, len_src_m1],
                seq_sort.clone(),
            );
            let x_src_init = self.ctx.terms.mk_app(
                Symbol::named("seq.++"),
                vec![sk_x, src_init],
                seq_sort.clone(),
            );
            let cnt_earlier = self.ctx.terms.mk_app(
                Symbol::named("seq.contains"),
                vec![x_src_init, src],
                ay_core::Sort::Bool,
            );
            // Track cnt_earlier so it gets contains axioms (#5998 R1 Finding 2).
            new_contains_terms.push((cnt_earlier, x_src_init, src));
            let not_cnt_earlier = self.ctx.terms.mk_not(cnt_earlier);
            axioms.push(self.ctx.terms.mk_or(vec![src_eq_empty, not_cnt_earlier]));

            // Length axioms for skolems.
            let len_x = self.mk_seq_len(sk_x);
            axioms.push(self.ctx.terms.mk_ge(len_x, zero));
            let len_y = self.mk_seq_len(sk_y);
            axioms.push(self.ctx.terms.mk_ge(len_y, zero));

            // Length of synthesized concat terms (not in scan).
            // len(x ++ src ++ y) = len(x) + len(src) + len(y)
            let len_x_src_y = self.mk_seq_len(x_src_y);
            let sum_lens = self.ctx.terms.mk_add(vec![len_x, len_src, len_y]);
            axioms.push(self.ctx.terms.mk_eq(len_x_src_y, sum_lens));

            // len(x ++ dst ++ y) = len(x) + len(dst) + len(y)
            let len_dst = self.mk_seq_len(dst);
            let len_x_dst_y = self.mk_seq_len(x_dst_y);
            let sum_dst_lens = self.ctx.terms.mk_add(vec![len_x, len_dst, len_y]);
            axioms.push(self.ctx.terms.mk_eq(len_x_dst_y, sum_dst_lens));

            // len(r) axiom: when guard holds, len(r) = len(u) - len(src) + len(dst)
            let len_u = self.mk_seq_len(u);
            let len_r = self.mk_seq_len(replace_term);
            let diff = self.ctx.terms.mk_sub(vec![len_u, len_src]);
            let expected_len = self.ctx.terms.mk_add(vec![diff, len_dst]);
            let r_len_eq = self.ctx.terms.mk_eq(len_r, expected_len);
            axioms.push(self.ctx.terms.mk_implies(guard, r_len_eq));

            // len(u) >= 0
            axioms.push(self.ctx.terms.mk_ge(len_u, zero));
        }

        (axioms, new_contains_terms)
    }
}
