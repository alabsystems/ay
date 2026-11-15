// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recursive materialization; a stopped word is never memoized.

use super::*;

impl BvSolver<'_> {
    /// Get or create bit representation for a BV term.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(super) fn get_bits(&mut self, term: TermId) -> BvBits {
        let counted = self.encoding.is_counted();
        let mut materialize = || {
            if !self.encoding_complete() {
                return Vec::new();
            }
            if let Some(bits) = self.term_to_bits.get(&term) {
                return self.counted_copy_bits(bits).unwrap_or_default();
            }

            let bits = self.bitblast(term);
            if !self.encoding_complete() {
                return Vec::new();
            }
            let Some(copied) = self.counted_copy_bits(&bits) else {
                return Vec::new();
            };
            if !counted::memory::map(&mut self.term_to_bits, &self.encoding) {
                return Vec::new();
            }
            self.probe_new_term_bits(term, &copied);
            self.term_to_bits.insert(term, copied);
            bits
        };
        // Counted preparation visits the typed DAG in postorder, so child words
        // are memo hits and no segmented recursion stack is allocated here.
        if counted {
            materialize()
        } else {
            stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, materialize)
        }
    }

    /// Bit-blast a bitvector term
    pub(super) fn bitblast(&mut self, term: TermId) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        let Some(data) = self.counted_term_data(term) else {
            return Vec::new();
        };

        match data {
            TermData::Const(Constant::BitVec { ref value, width }) => {
                // Constant: create bits from value.
                // Zero bits use `fresh_false` to track in `known_false` for multiplication
                // optimization (#1720).
                let Some(mut bits) = self.counted_bits(width as usize) else {
                    return Vec::new();
                };
                for i in 0..width {
                    if !self.encoding_step() {
                        return Vec::new();
                    }
                    let bit_set = value.bit(u64::from(i));
                    let lit = if bit_set {
                        // Use the canonical true representation recognized by
                        // `is_known_true`, matching `const_bits`. Previously
                        // positive unit literals here looked variable to every
                        // constant-propagation and multiplier shortcut.
                        neg_lit(self.fresh_false())
                    } else {
                        self.fresh_false()
                    };
                    bits.push(lit);
                }
                bits
            }
            TermData::Var(ref _name, _) => {
                // Variable: allocate fresh boolean variables
                let width = match self.terms.sort(term) {
                    Sort::BitVec(bv) => bv.width,
                    _ => return Vec::new(),
                };
                self.counted_fresh_bits(width as usize)
            }
            TermData::Ite(cond, then_term, else_term) => {
                let Sort::BitVec(_) = self.terms.sort(term) else {
                    return Vec::new();
                };
                self.bitblast_ite_flattened(cond, then_term, else_term)
            }
            TermData::App(ref sym, ref args) => self.bitblast_app(term, sym, args),
            _ => {
                // Unknown term type - allocate fresh bits
                if let Sort::BitVec(bv) = self.terms.sort(term) {
                    self.counted_fresh_bits(bv.width as usize)
                } else {
                    Vec::new()
                }
            }
        }
    }

    /// Return fresh unconstrained bits for the given term's sort width.
    /// Used as fallback when bitblasting encounters width mismatches (#5595).
    pub(super) fn fresh_bits_for_term(&mut self, term: TermId) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            self.counted_fresh_bits(bv.width as usize)
        } else {
            Vec::new()
        }
    }

    /// Get bits for a binary BV operation, returning None if operands have
    /// mismatched widths (0 bits from non-BV sub-terms). (#5595)
    pub(super) fn get_binary_bits(&mut self, a: TermId, b: TermId) -> Option<(BvBits, BvBits)> {
        let a_bits = self.get_bits(a);
        let b_bits = self.get_bits(b);
        if a_bits.is_empty() || b_bits.is_empty() || a_bits.len() != b_bits.len() {
            None
        } else {
            Some((a_bits, b_bits))
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
        if !self.encoding_complete() {
            return Vec::new();
        }
        // The counted source walk already materialized every child. Preserve
        // this DAG sharing instead of allocating an optional flattening spine.
        if self.encoding.is_counted() {
            return self.counted_bv_ite(cond, then_term, else_term);
        }

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
            if !self.encoding_step() {
                return Vec::new();
            }
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
            if !self.encoding_step() {
                return Vec::new();
            }
            self.bv_ite_conditions.insert(c);
        }

        // Build the MUX tree from bottom up (right to left).
        // Start with the default (final else) value.
        let mut result = self.get_bits(cur_else);

        // Process cases in reverse order to build right-leaning MUX tree
        for &(c, v) in cases.iter().rev() {
            if !self.encoding_step() {
                return Vec::new();
            }
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
    pub(super) fn bitblast_concat_flattened(&mut self, term: TermId) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        if self.encoding.is_counted() {
            return self.counted_concat(term);
        }

        let mut stack = vec![term];
        let mut leaves = Vec::new();
        let mut total_width = 0usize;

        while let Some(t) = stack.pop() {
            if !self.encoding_step() {
                return Vec::new();
            }
            match self.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "concat" && !args.is_empty() => {
                    for &arg in args {
                        if !self.encoding_step() {
                            return Vec::new();
                        }
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
            // Only the result's pre-sizing hint, so it saturates.
            total_width = total_width.saturating_add(width);
            leaves.push(t);
        }

        let mut result = bits_with_capacity(total_width);
        for leaf in leaves {
            if !self.encoding_step() {
                return Vec::new();
            }
            let bits = self.get_bits(leaf);
            result.extend(bits);
        }
        result
    }

    pub(super) fn const_bits(&mut self, value: u64, width: usize) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }

        // Reserved fallibly: the reservation is only a pre-sizing hint, so a
        // refused one forgoes it and `push` below grows the vector itself.
        let Some(mut bits) = self.counted_bits(width) else {
            return Vec::new();
        };
        for i in 0..width {
            if !self.encoding_step() {
                return Vec::new();
            }
            // `value` is a `u64`, but BV widths can exceed 64. Treat higher bits as 0.
            let bit_set = if i < u64::BITS as usize {
                (value >> i) & 1 == 1
            } else {
                false
            };
            let var = if bit_set {
                // Use negation of cached false literal so that `is_known_true`
                // recognizes constant-true bits flowing through gates.
                // This enables constant propagation in AND/OR/XOR/MUX gates
                // when one input comes from a BV constant. (#7974)
                neg_lit(self.fresh_false())
            } else {
                self.fresh_false()
            };
            bits.push(var);
        }
        bits
    }
    /// Same repeated literal with cooperative bounded-chunk refusal.
    pub(super) fn repeat_bit(&self, bit: CnfLit, n: usize) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        let Some(mut bits) = self.counted_bits(n) else {
            return Vec::new();
        };
        for _ in 0..n {
            if !self.encoding_step() {
                return Vec::new();
            }
            bits.push(bit);
        }
        bits
    }
}
