// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF gate and mux encoding helpers.

use super::*;

mod simplification;

/// Complement of a CNF literal: `neg_lit(lit) == -lit` for every literal.
///
/// CNF literals are DIMACS `±var` with `var` in `1..=i32::MAX`, a domain on
/// which negation never overflows, so `wrapping_neg` is total and identical to
/// `-lit` there. This is the same form as ay-core's own literal complement
/// (`Tseitin::negate`, crates/ay-core/src/tseitin/mod.rs). `i32::MIN` is not a
/// literal of any variable; it is the one value `wrapping_neg` maps to itself.
#[inline]
const fn neg_lit(lit: CnfLit) -> CnfLit {
    lit.wrapping_neg()
}

impl BvSolver<'_> {
    /// Create AND gate: out = a AND b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: if either input is known true/false, the gate
    /// is resolved without allocating a fresh variable or adding clauses.
    /// This is critical for QF_ABV where BV constants produce many
    /// known-constant bits flowing through arithmetic circuits.
    pub(super) fn mk_and(&mut self, mut a: CnfLit, mut b: CnfLit) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        loop {
            if !self.encoding_step() {
                return 0;
            }
            if let Some(lit) = self.simplify_and_level1(a, b) {
                return lit;
            }

            let a_children = self.and_children_of(a);
            let b_children = self.and_children_of(b);
            let a_is_and = a_children.is_some();
            let b_is_and = b_children.is_some();
            let a_is_neg = a < 0;
            let b_is_neg = b < 0;
            let (x, y) = a_children.unwrap_or((0, 0));
            let (z, w) = b_children.unwrap_or((0, 0));

            // Level 2: contradiction, subsumption, idempotence, resolution.
            if !a_is_neg && a_is_and && (x == neg_lit(b) || y == neg_lit(b)) {
                return self.fresh_false();
            }
            if !b_is_neg && b_is_and && (z == neg_lit(a) || w == neg_lit(a)) {
                return self.fresh_false();
            }
            if !a_is_neg
                && !b_is_neg
                && a_is_and
                && b_is_and
                && (x == neg_lit(z) || x == neg_lit(w) || y == neg_lit(z) || y == neg_lit(w))
            {
                return self.fresh_false();
            }
            if a_is_neg && a_is_and && (x == neg_lit(b) || y == neg_lit(b)) {
                return b;
            }
            if b_is_neg && b_is_and && (z == neg_lit(a) || w == neg_lit(a)) {
                return a;
            }
            if a_is_neg
                && !b_is_neg
                && a_is_and
                && b_is_and
                && (x == neg_lit(z) || x == neg_lit(w) || y == neg_lit(z) || y == neg_lit(w))
            {
                return b;
            }
            if b_is_neg
                && !a_is_neg
                && b_is_and
                && a_is_and
                && (z == neg_lit(x) || z == neg_lit(y) || w == neg_lit(x) || w == neg_lit(y))
            {
                return a;
            }
            if !a_is_neg && a_is_and && (x == b || y == b) {
                return a;
            }
            if !b_is_neg && b_is_and && (z == a || w == a) {
                return b;
            }
            if a_is_neg && b_is_neg && a_is_and && b_is_and {
                if (x == z && y == neg_lit(w)) || (x == w && y == neg_lit(z)) {
                    return neg_lit(x);
                }
                if (w == y && z == neg_lit(x)) || (w == x && z == neg_lit(y)) {
                    return neg_lit(w);
                }
            }

            // Level 3: substitution rules rewrite one operand and retry.
            if a_is_neg && a_is_and {
                if x == b {
                    a = neg_lit(y);
                    continue;
                }
                if y == b {
                    a = neg_lit(x);
                    continue;
                }
            }
            if b_is_neg && b_is_and {
                if z == a {
                    b = neg_lit(w);
                    continue;
                }
                if w == a {
                    b = neg_lit(z);
                    continue;
                }
            }
            if a_is_neg && !b_is_neg && a_is_and && b_is_and {
                if x == z || x == w {
                    a = neg_lit(y);
                    continue;
                }
                if y == z || y == w {
                    a = neg_lit(x);
                    continue;
                }
            }
            if b_is_neg && !a_is_neg && b_is_and && a_is_and {
                if z == x || z == y {
                    b = neg_lit(w);
                    continue;
                }
                if w == x || w == y {
                    b = neg_lit(z);
                    continue;
                }
            }

            // Level 4: AND/AND idempotence rewrites one child and retries.
            if !a_is_neg && !b_is_neg && a_is_and && b_is_and {
                if x == z || y == z {
                    b = w;
                    continue;
                }
                if x == w || y == w {
                    b = z;
                    continue;
                }
            }

            break;
        }

        // Normalize key for cache lookup (commutative operation)
        let key = Self::normalize_commutative_gate_key(a, b);

        // Check cache first
        if let Some(&cached) = self.and_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // out => a: (-out OR a)
        // out => b: (-out OR b)
        // a AND b => out: (-a OR -b OR out)
        self.emit_clause(&[neg_lit(out), a]);
        self.emit_clause(&[neg_lit(out), b]);
        self.emit_clause(&[neg_lit(a), neg_lit(b), out]);

        // Cache the result
        if !self.encoding.was_stopped() && counted::memory::map(&mut self.and_cache, &self.encoding)
        {
            self.and_cache.insert(key, out);
        }
        if !self.encoding.was_stopped()
            && counted::memory::map(&mut self.and_children, &self.encoding)
        {
            self.and_children.insert(out, key);
        }
        out
    }

    /// Create OR gate: out = a OR b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: if either input is known true/false, the gate
    /// is resolved without allocating a fresh variable or adding clauses.
    /// Non-trivial ORs lower through De Morgan so OR-derived structure feeds
    /// the same two-level AIG simplifier and AND cache as native AND gates.
    pub(super) fn mk_or(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        // Trivial simplifications
        // a OR a = a
        if a == b {
            return a;
        }
        // a OR NOT(a) = true
        if a == neg_lit(b) {
            return self.fresh_true();
        }
        // Constant propagation: false OR b = b, true OR b = true
        if self.is_known_false(a) {
            return b;
        }
        if self.is_known_false(b) {
            return a;
        }
        if self.is_known_true(a) {
            return a; // a is already a known-true literal
        }
        if self.is_known_true(b) {
            return b;
        }

        // Normalize key for cache lookup (commutative operation)
        let key = Self::normalize_commutative_gate_key(a, b);

        // Check cache first
        if let Some(&cached) = self.or_cache.get(&key) {
            return cached;
        }

        let out = neg_lit(self.mk_and(neg_lit(a), neg_lit(b)));
        if !self.encoding.was_stopped() && counted::memory::map(&mut self.or_cache, &self.encoding)
        {
            self.or_cache.insert(key, out);
        }
        out
    }

    /// Create XOR gate: out = a XOR b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: false XOR b = b, true XOR b = NOT(b).
    pub(super) fn mk_xor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        // Trivial simplifications
        // a XOR a = false
        if a == b {
            return self.fresh_false();
        }
        // a XOR NOT(a) = true
        if a == neg_lit(b) {
            return self.fresh_true();
        }
        // Constant propagation: false XOR b = b, true XOR b = NOT(b)
        if self.is_known_false(a) {
            return b;
        }
        if self.is_known_false(b) {
            return a;
        }
        if self.is_known_true(a) {
            return neg_lit(b); // true XOR b = NOT(b)
        }
        if self.is_known_true(b) {
            return neg_lit(a); // a XOR true = NOT(a)
        }

        if let Some(lit) = self.simplify_xor_split_ands(a, b) {
            return lit;
        }
        if let Some(lit) = self.simplify_xor_with_and_child(a, b) {
            return lit;
        }
        if let Some(lit) = self.simplify_xor_with_and_child(b, a) {
            return lit;
        }

        // Normalize key for cache lookup (commutative operation)
        let key = if a < b { (a, b) } else { (b, a) };

        // Check cache first
        if let Some(&cached) = self.xor_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // XOR truth table:
        // a=0, b=0 => out=0
        // a=0, b=1 => out=1
        // a=1, b=0 => out=1
        // a=1, b=1 => out=0
        // Clauses:
        // (-a OR -b OR -out)
        // (-a OR b OR out)
        // (a OR -b OR out)
        // (a OR b OR -out)
        self.emit_clause(&[neg_lit(a), neg_lit(b), neg_lit(out)]);
        self.emit_clause(&[neg_lit(a), b, out]);
        self.emit_clause(&[a, neg_lit(b), out]);
        self.emit_clause(&[a, b, neg_lit(out)]);

        // Cache the result
        if !self.encoding.was_stopped() && counted::memory::map(&mut self.xor_cache, &self.encoding)
        {
            self.xor_cache.insert(key, out);
        }
        if self.capture_gate_provenance {
            if !self.encoding.was_stopped()
                && counted::memory::map(&mut self.xor_children, &self.encoding)
            {
                self.xor_children.insert(out, key);
            }
        }
        out
    }

    /// Create XNOR gate: out = a XNOR b = NOT(a XOR b)
    pub(super) fn mk_xnor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        let xor = self.mk_xor(a, b);
        neg_lit(xor)
    }

    /// Create AND of many literals
    pub(super) fn mk_and_many(&mut self, lits: &[CnfLit]) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        let Some((&first, rest)) = lits.split_first() else {
            return self.fresh_true();
        };
        if rest.is_empty() {
            return first;
        }

        let mut result = first;
        for &lit in rest {
            if !self.encoding_step() {
                return 0;
            }
            result = self.mk_and(result, lit);
        }
        result
    }

    /// Create MUX: if sel then a else b (bitwise)
    pub(super) fn bitwise_mux(&mut self, a: &BvBits, b: &BvBits, sel: CnfLit) -> BvBits {
        if !self.encoding_complete() {
            return Vec::new();
        }
        assert_eq!(a.len(), b.len());
        let Some(mut result) = self.counted_bits(a.len()) else {
            return Vec::new();
        };
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            if !self.encoding_step() {
                return Vec::new();
            }
            result.push(self.mk_mux(ai, bi, sel));
        }
        result
    }

    /// Create MUX: if sel then a else b
    ///
    /// Uses structural hashing to avoid duplicate MUX gates (#8143).
    /// Constant propagation: known selector, equal inputs, and known data
    /// inputs are resolved without allocating a fresh variable.
    pub(super) fn mk_mux(&mut self, a: CnfLit, b: CnfLit, sel: CnfLit) -> CnfLit {
        if !self.encoding_step() {
            return 0; // Private stopped unwind, never exported as a gate.
        }

        // Known selector: sel=true => a, sel=false => b
        if self.is_known_true(sel) {
            return a;
        }
        if self.is_known_false(sel) {
            return b;
        }
        // Both branches equal: result is just that value
        if a == b {
            return a;
        }
        // Branches are complements: (ite sel a (NOT a)) ≡ (sel ↔ a) ≡ XNOR(sel, a)
        // Since b = ¬a, we must use `a` (not `b`) for the XNOR.
        // Using `b` would compute XNOR(sel, ¬a) = ¬(sel ↔ a), which is inverted.
        if a == neg_lit(b) {
            return self.mk_xnor(sel, a);
        }

        // Data-input constant propagation (#7974): when a branch is a known
        // constant, the MUX reduces to a simpler gate that reuses existing
        // AND/OR infrastructure (with its own structural hashing and constant
        // propagation). Each avoided MUX saves 1 fresh variable + 4 clauses.
        //
        // ite(sel, true,  b) = sel ∨ b
        // ite(sel, false, b) = ¬sel ∧ b
        // ite(sel, a, true)  = ¬sel ∨ a
        // ite(sel, a, false) = sel ∧ a
        if self.is_known_true(a) {
            return self.mk_or(sel, b);
        }
        if self.is_known_false(a) {
            return self.mk_and(neg_lit(sel), b);
        }
        if self.is_known_true(b) {
            return self.mk_or(neg_lit(sel), a);
        }
        if self.is_known_false(b) {
            return self.mk_and(sel, a);
        }

        // MUX cache lookup: key is (sel, a, b) — NOT commutative (#8143)
        let key = (sel, a, b);
        if let Some(&cached) = self.mux_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // out = (sel AND a) OR (NOT sel AND b)
        // Clauses:
        // (-sel OR -a OR out)  -- sel=1, a=1 => out=1
        // (-sel OR a OR -out)  -- sel=1, a=0 => out=0
        // (sel OR -b OR out)   -- sel=0, b=1 => out=1
        // (sel OR b OR -out)   -- sel=0, b=0 => out=0
        self.emit_clause(&[neg_lit(sel), neg_lit(a), out]);
        self.emit_clause(&[neg_lit(sel), a, neg_lit(out)]);
        self.emit_clause(&[sel, neg_lit(b), out]);
        self.emit_clause(&[sel, b, neg_lit(out)]);

        // Cache the result
        if !self.encoding.was_stopped() && counted::memory::map(&mut self.mux_cache, &self.encoding)
        {
            self.mux_cache.insert(key, out);
        }
        if self.capture_gate_provenance {
            if !self.encoding.was_stopped()
                && counted::memory::map(&mut self.mux_children, &self.encoding)
            {
                self.mux_children.insert(out, key);
            }
        }
        out
    }
}
