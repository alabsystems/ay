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
        if !self.encoding_complete() {
            return Vec::new();
        }

        let name = sym.name();

        // Check if this operation should be delayed (#7015).
        // For expensive operations (mul/div/rem on wide BV with 2+ variable args),
        // allocate fresh unconstrained bits and record the operation for later
        // checking against the SAT model.
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            if !self.encoding.is_counted() && self.should_delay(term, name, args, bv.width) {
                let width = bv.width as usize;
                let bits = self.batch_fresh_vars(width).to_vec();
                // Ensure argument bits are materialized (needed for model evaluation)
                for &arg in args {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
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
                if !self.encoding_complete() {
                    return Vec::new();
                }
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
                self.bitblast_not(&a)
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
                if !self.encoding_complete() {
                    return Vec::new();
                }
                debug_assert_eq!(
                    a.len(),
                    b.len(),
                    "bvcomp operands have different widths: {} vs {}",
                    a.len(),
                    b.len()
                );
                if a.len() != b.len() {
                    // Fallback: return unconstrained variable rather than panic.
                    let bit = self.fresh_var();
                    self.counted_copy_bits(&[bit]).unwrap_or_default()
                } else {
                    let eq = self.bitblast_eq(&a, &b);
                    self.counted_copy_bits(&[eq]).unwrap_or_default()
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
            "mkbv" => {
                let Some(mut bits) = self.counted_bits(args.len()) else {
                    return Vec::new();
                };
                bits.extend(args.iter().map(|&arg| self.bitblast_bool(arg)));
                bits
            }
            "concat" => self.bitblast_concat_flattened(term),
            "extract" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() >= 2 {
                        let hi = indices[0] as usize;
                        let lo = indices[1] as usize;
                        if lo <= hi && hi < x_bits.len() {
                            return self.counted_copy_bits(&x_bits[lo..=hi]).unwrap_or_default();
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
                        if !counted::memory::reserve(&mut result, extension_bits, &self.encoding) {
                            return Vec::new();
                        }
                        let false_lit = self.fresh_false();
                        for _ in 0..extension_bits {
                            if !self.encoding_step() {
                                return Vec::new();
                            }
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
                        let Some(mut result) = self.counted_copy_bits(&x_bits) else {
                            return Vec::new();
                        };
                        if !counted::memory::reserve(&mut result, extension_bits, &self.encoding) {
                            return Vec::new();
                        }
                        let sign_bit = if let Some(&bit) = x_bits.last() {
                            bit
                        } else {
                            self.fresh_false()
                        };
                        for _ in 0..extension_bits {
                            if !self.encoding_step() {
                                return Vec::new();
                            }
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

                let Some(width) = x_bits.len().checked_mul(copies) else {
                    counted::memory::storage(&self.encoding);
                    return Vec::new();
                };
                let Some(mut result) = self.counted_bits(width) else {
                    return Vec::new();
                };
                for _ in 0..copies {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
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

                let Some(mut result) = self.counted_bits(n) else {
                    return Vec::new();
                };
                for i in 0..n {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
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

                let Some(mut result) = self.counted_bits(n) else {
                    return Vec::new();
                };
                for i in 0..n {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
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
                if self.encoding.is_counted() {
                    self.counted_unsupported("unaccounted BV application");
                    Vec::new()
                } else {
                    self.batch_fresh_vars(width as usize).to_vec()
                }
            }
        }
    }
}
