// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV function application dispatch and concat flattening.
//!
//! Routes BV operations to their bit-blasting implementations.
//! Arithmetic, bitwise, and multiplication primitives are in
//! `arithmetic_ops`.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast a function application
    pub(super) fn bitblast_app(&mut self, term: TermId, sym: &Symbol, args: &[TermId]) -> BvBits {
        let name = sym.name();

        // Check if this operation should be delayed (#7015).
        // For expensive operations (mul/div/rem on wide BV with 2+ variable args),
        // allocate fresh unconstrained bits and record the operation for later
        // checking against the SAT model.
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            if self.should_delay(term, name, args, bv.width) {
                let width = bv.width as usize;
                let bits = self.batch_fresh_vars(width).to_vec();
                // Ensure argument bits are materialized (needed for model evaluation)
                for &arg in args {
                    if matches!(self.terms.sort(arg), Sort::BitVec(_)) {
                        let _ = self.get_bits(arg);
                    }
                }
                let op_name = match name {
                    "bvmul" => "bvmul",
                    "bvadd" => "bvadd",
                    "bvudiv" => "bvudiv",
                    "bvurem" => "bvurem",
                    "bvsdiv" => "bvsdiv",
                    "bvsrem" => "bvsrem",
                    "bvsmod" => "bvsmod",
                    _ => "unknown",
                };
                self.delayed_ops.push(DelayedBvOp {
                    term,
                    op: op_name,
                    args: args.to_vec(),
                    result_bits: bits.clone(),
                    circuit_built: false,
                    cheap_tries: 0,
                });

                // No proactive structural clauses for delayed ops (#8480).
                //
                // Previously, trailing-zero clauses (OR-chain encoding) were
                // added for delayed bvmul to help the SAT solver prune.
                // However, these clauses interact with SAT preprocessing and
                // other formula constraints to derive spurious UNSAT on
                // satisfiable formulas (the unconstrained result bits get
                // forced to values that conflict with equalities elsewhere).
                //
                // The post-solve re-check loop (#8480 fix) handles correctness:
                // - Phase 1: cheap axioms detect zero/one/power-of-2 violations
                // - Phase 2: full circuit construction for remaining violations
                // Without structural clauses, the initial SAT solve always has
                // a satisfying assignment (unconstrained bits = any value), so
                // the re-check loop is guaranteed to fire.

                return bits;
            }
        }

        match name {
            "bvadd" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_add(&a, &b)
            }
            "bvsub" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_sub(&a, &b)
            }
            "bvmul" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_mul(&a, &b)
            }
            "bvand" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_and(&a, &b)
            }
            "bvor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_or(&a, &b)
            }
            "bvxor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_xor(&a, &b)
            }
            "bvnand" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_nand(&a, &b)
            }
            "bvnor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_nor(&a, &b)
            }
            "bvxnor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_xnor(&a, &b)
            }
            "bvnot" => {
                let a = self.get_bits(args[0]);
                Self::bitblast_not(&a)
            }
            "bvneg" => {
                let a = self.get_bits(args[0]);
                self.bitblast_neg(&a)
            }
            "bvcomp" => {
                let a = self.get_bits(args[0]);
                let b = self.get_bits(args[1]);
                // SMT-LIB requires both operands to have the same width.
                // Guard against upstream sort mismatch (#5602).
                debug_assert_eq!(
                    a.len(),
                    b.len(),
                    "bvcomp operands have different widths: {} vs {}",
                    a.len(),
                    b.len()
                );
                if a.len() != b.len() {
                    // Fallback: return unconstrained variable rather than panic.
                    vec![self.fresh_var()]
                } else {
                    let eq = self.bitblast_eq(&a, &b);
                    vec![eq]
                }
            }
            "bvshl" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_shl(&a, &b)
            }
            "bvlshr" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_lshr(&a, &b)
            }
            "bvashr" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_ashr(&a, &b)
            }
            "bvudiv" => {
                // Share division circuit with bvurem (#4873)
                let (q, _) = self.bitblast_udiv_urem_cached(args[0], args[1]);
                q
            }
            "bvurem" => {
                // Share division circuit with bvudiv (#4873)
                let (_, r) = self.bitblast_udiv_urem_cached(args[0], args[1]);
                r
            }
            "bvsdiv" => {
                // Share signed division circuit with bvsrem (#4873)
                let (abs_q, _, sign_a, sign_b) =
                    self.bitblast_signed_div_rem_cached(args[0], args[1]);
                if abs_q.is_empty() {
                    return Vec::new();
                }
                let result_neg = self.mk_xor(sign_a, sign_b);
                self.conditional_neg(&abs_q, result_neg)
            }
            "bvsrem" => {
                // Share signed division circuit with bvsdiv (#4873)
                let (_, abs_r, sign_a, _) = self.bitblast_signed_div_rem_cached(args[0], args[1]);
                if abs_r.is_empty() {
                    return Vec::new();
                }
                self.conditional_neg(&abs_r, sign_a)
            }
            "bvsmod" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_smod(&a, &b)
            }
            "concat" => self.bitblast_concat_flattened(term),
            "extract" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() >= 2 {
                        let hi = indices[0] as usize;
                        let lo = indices[1] as usize;
                        if lo <= hi && hi < x_bits.len() {
                            return x_bits[lo..=hi].to_vec();
                        }
                    }
                }
                self.fresh_bits_for_term(term)
            }
            "zero_extend" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if let Some(&i) = indices.first() {
                        let extension_bits = i as usize;
                        let mut result = x_bits;
                        let false_lit = self.fresh_false();
                        for _ in 0..extension_bits {
                            result.push(false_lit);
                        }
                        return result;
                    }
                }
                x_bits
            }
            "sign_extend" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if let Some(&i) = indices.first() {
                        let extension_bits = i as usize;
                        let mut result = x_bits.clone();
                        let sign_bit = if let Some(&bit) = x_bits.last() {
                            bit
                        } else {
                            self.fresh_false()
                        };
                        for _ in 0..extension_bits {
                            result.push(sign_bit);
                        }
                        return result;
                    }
                }
                x_bits
            }
            "repeat" => {
                let x_bits = self.get_bits(args[0]);
                let copies = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(1)
                } else {
                    1
                } as usize;

                if copies == 0 || x_bits.is_empty() {
                    return Vec::new();
                }
                if copies == 1 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(x_bits.len() * copies);
                for _ in 0..copies {
                    result.extend_from_slice(&x_bits);
                }
                result
            }
            "rotate_left" => {
                let x_bits = self.get_bits(args[0]);
                let n = x_bits.len();
                if n <= 1 {
                    return x_bits;
                }

                let k = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(0) as usize
                } else {
                    0
                } % n;

                if k == 0 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(n);
                for i in 0..n {
                    let src = (i + n - k) % n;
                    result.push(x_bits[src]);
                }
                result
            }
            "rotate_right" => {
                let x_bits = self.get_bits(args[0]);
                let n = x_bits.len();
                if n <= 1 {
                    return x_bits;
                }

                let k = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(0) as usize
                } else {
                    0
                } % n;

                if k == 0 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(n);
                for i in 0..n {
                    let src = (i + k) % n;
                    result.push(x_bits[src]);
                }
                result
            }
            _ => {
                let width = match self.terms.sort(term) {
                    Sort::BitVec(bv) => bv.width,
                    // Ill-sorted input: degrade gracefully like the other
                    // bitblast() arms (Var/Ite/unknown-term all return an
                    // empty bit vector as the not-a-BV signal) instead of
                    // panicking the whole solve.
                    _ => return Vec::new(),
                };
                self.batch_fresh_vars(width as usize).to_vec()
            }
        }
    }

    /// Flatten nested BV ITE chains and bitblast with shared selectors (#8143).
    ///
    /// For a chain like `(ite c1 (ite c2 a b) (ite c3 c d))`, this collects
    /// all (condition, value) leaf pairs from the right-leaning (else) spine
    /// and builds a priority-encoded multiplexer:
    ///   result = mux(c1, then_bits, mux(c3, c_bits, d_bits))
    ///
    /// The flattening reduces nesting depth without changing semantics.
    /// The MUX gate cache (#8143) ensures that identical (sel, a, b) triples
    /// across the tree share SAT variables.
    ///
    /// For shallow ITEs (depth <= 2), this falls through to the standard
    /// bitwise_mux encoding to avoid overhead from the flattening traversal.
    pub(super) fn bitblast_ite_flattened(
        &mut self,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> BvBits {
        // Collect the ITE chain as a list of (condition, value) pairs.
        // The chain is collected along the else-spine:
        //   (ite c1 v1 (ite c2 v2 (ite c3 v3 default)))
        //   => [(c1, v1), (c2, v2), (c3, v3)] + default
        let mut cases: Vec<(TermId, TermId)> = Vec::new();
        let mut cur_cond = cond;
        let mut cur_then = then_term;
        let mut cur_else = else_term;
        // Limit flattening depth to avoid pathological cases
        const MAX_FLATTEN_DEPTH: usize = 32;

        loop {
            cases.push((cur_cond, cur_then));
            if cases.len() >= MAX_FLATTEN_DEPTH {
                break;
            }
            // Check if the else branch is another ITE with the same sort.
            // Only flatten if the else branch is NOT already cached (to avoid
            // redundant work when the else branch is shared with other terms).
            if self.term_to_bits.contains_key(&cur_else) {
                break;
            }
            let else_data = self.terms.get(cur_else).clone();
            match else_data {
                TermData::Ite(c, t, e) => {
                    if !matches!(self.terms.sort(cur_else), Sort::BitVec(_)) {
                        break;
                    }
                    cur_cond = c;
                    cur_then = t;
                    cur_else = e;
                }
                _ => break,
            }
        }

        // If the chain is trivial (just one ITE), fall through to standard encoding
        if cases.len() <= 1 {
            // Track this condition for Tseitin linking (#1696)
            self.bv_ite_conditions.insert(cond);
            let sel = self.bitblast_bool(cond);
            let t_bits = self.get_bits(then_term);
            let e_bits = self.get_bits(else_term);
            return self.bitwise_mux(&t_bits, &e_bits, sel);
        }

        // Track all conditions for Tseitin linking (#1696)
        for &(c, _) in &cases {
            self.bv_ite_conditions.insert(c);
        }

        // Build the MUX tree from bottom up (right to left).
        // Start with the default (final else) value.
        let mut result = self.get_bits(cur_else);

        // Process cases in reverse order to build right-leaning MUX tree
        for &(c, v) in cases.iter().rev() {
            let sel = self.bitblast_bool(c);
            let v_bits = self.get_bits(v);
            if v_bits.len() != result.len() {
                // Width mismatch -- fall back to standard encoding for safety
                break;
            }
            result = self.bitwise_mux(&v_bits, &result, sel);
        }

        result
    }

    /// Flatten nested concat and bitblast in one pass.
    fn bitblast_concat_flattened(&mut self, term: TermId) -> BvBits {
        let mut stack = vec![term];
        let mut leaves = Vec::new();
        let mut total_width = 0usize;

        while let Some(t) = stack.pop() {
            match self.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "concat" && !args.is_empty() => {
                    for &arg in args {
                        stack.push(arg);
                    }
                    continue;
                }
                _ => {}
            }
            let width = match self.terms.sort(t) {
                Sort::BitVec(bv) => bv.width as usize,
                _ => 0,
            };
            total_width += width;
            leaves.push(t);
        }

        let mut result = Vec::with_capacity(total_width);
        for leaf in leaves {
            let bits = self.get_bits(leaf);
            result.extend(bits);
        }
        result
    }
}
