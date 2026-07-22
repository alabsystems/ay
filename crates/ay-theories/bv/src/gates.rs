// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF gate and mux encoding helpers.

use super::*;

impl BvSolver<'_> {
    fn normalize_commutative_gate_key(a: CnfLit, b: CnfLit) -> (CnfLit, CnfLit) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }

    fn and_children_of(&self, lit: CnfLit) -> Option<(CnfLit, CnfLit)> {
        self.and_children.get(&lit.abs()).copied()
    }

    fn simplify_and_level1(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(a);
        }
        if a == -b {
            return Some(self.fresh_false());
        }
        if self.is_known_true(a) {
            return Some(b);
        }
        if self.is_known_true(b) {
            return Some(a);
        }
        if self.is_known_false(a) {
            return Some(a);
        }
        if self.is_known_false(b) {
            return Some(b);
        }
        None
    }

    fn split_common_complement(left: (CnfLit, CnfLit), right: (CnfLit, CnfLit)) -> Option<CnfLit> {
        let (a, b) = left;
        let (c, d) = right;

        if a == c && b == -d {
            return Some(a);
        }
        if a == d && b == -c {
            return Some(a);
        }
        if b == c && a == -d {
            return Some(b);
        }
        if b == d && a == -c {
            return Some(b);
        }
        None
    }

    fn simplify_xor_split_ands(&self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        let a_children = self.and_children_of(a)?;
        let b_children = self.and_children_of(b)?;
        let common = Self::split_common_complement(a_children, b_children)?;

        if (a < 0) == (b < 0) {
            Some(common)
        } else {
            Some(-common)
        }
    }

    fn simplify_xor_with_and_child(&mut self, and_lit: CnfLit, other: CnfLit) -> Option<CnfLit> {
        let (x, y) = self.and_children_of(and_lit)?;
        let and_is_negated = and_lit < 0;

        if other == x {
            return Some(if and_is_negated {
                self.mk_or(-x, y)
            } else {
                self.mk_and(x, -y)
            });
        }
        if other == y {
            return Some(if and_is_negated {
                self.mk_or(x, -y)
            } else {
                self.mk_and(-x, y)
            });
        }
        if other == -x {
            return Some(if and_is_negated {
                self.mk_and(x, -y)
            } else {
                self.mk_or(-x, y)
            });
        }
        if other == -y {
            return Some(if and_is_negated {
                self.mk_and(-x, y)
            } else {
                self.mk_or(x, -y)
            });
        }

        None
    }

    pub(super) fn const_bits(&mut self, value: u64, width: usize) -> BvBits {
        let mut bits = Vec::with_capacity(width);
        for i in 0..width {
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
                -self.fresh_false()
            } else {
                self.fresh_false()
            };
            bits.push(var);
        }
        bits
    }

    /// Create AND gate: out = a AND b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: if either input is known true/false, the gate
    /// is resolved without allocating a fresh variable or adding clauses.
    /// This is critical for QF_ABV where BV constants produce many
    /// known-constant bits flowing through arithmetic circuits.
    pub(super) fn mk_and(&mut self, mut a: CnfLit, mut b: CnfLit) -> CnfLit {
        loop {
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
            if !a_is_neg && a_is_and && (x == -b || y == -b) {
                return self.fresh_false();
            }
            if !b_is_neg && b_is_and && (z == -a || w == -a) {
                return self.fresh_false();
            }
            if !a_is_neg
                && !b_is_neg
                && a_is_and
                && b_is_and
                && (x == -z || x == -w || y == -z || y == -w)
            {
                return self.fresh_false();
            }
            if a_is_neg && a_is_and && (x == -b || y == -b) {
                return b;
            }
            if b_is_neg && b_is_and && (z == -a || w == -a) {
                return a;
            }
            if a_is_neg
                && !b_is_neg
                && a_is_and
                && b_is_and
                && (x == -z || x == -w || y == -z || y == -w)
            {
                return b;
            }
            if b_is_neg
                && !a_is_neg
                && b_is_and
                && a_is_and
                && (z == -x || z == -y || w == -x || w == -y)
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
                if (x == z && y == -w) || (x == w && y == -z) {
                    return -x;
                }
                if (w == y && z == -x) || (w == x && z == -y) {
                    return -w;
                }
            }

            // Level 3: substitution rules rewrite one operand and retry.
            if a_is_neg && a_is_and {
                if x == b {
                    a = -y;
                    continue;
                }
                if y == b {
                    a = -x;
                    continue;
                }
            }
            if b_is_neg && b_is_and {
                if z == a {
                    b = -w;
                    continue;
                }
                if w == a {
                    b = -z;
                    continue;
                }
            }
            if a_is_neg && !b_is_neg && a_is_and && b_is_and {
                if x == z || x == w {
                    a = -y;
                    continue;
                }
                if y == z || y == w {
                    a = -x;
                    continue;
                }
            }
            if b_is_neg && !a_is_neg && b_is_and && a_is_and {
                if z == x || z == y {
                    b = -w;
                    continue;
                }
                if w == x || w == y {
                    b = -z;
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
        self.add_clause(CnfClause::binary(-out, a));
        self.add_clause(CnfClause::binary(-out, b));
        self.add_clause(CnfClause::new(vec![-a, -b, out]));

        // Cache the result
        self.and_cache.insert(key, out);
        self.and_children.insert(out, key);
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
        // Trivial simplifications
        // a OR a = a
        if a == b {
            return a;
        }
        // a OR NOT(a) = true
        if a == -b {
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

        let out = -self.mk_and(-a, -b);
        self.or_cache.insert(key, out);
        out
    }

    /// Create XOR gate: out = a XOR b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: false XOR b = b, true XOR b = NOT(b).
    pub(super) fn mk_xor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        // Trivial simplifications
        // a XOR a = false
        if a == b {
            return self.fresh_false();
        }
        // a XOR NOT(a) = true
        if a == -b {
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
            return -b; // true XOR b = NOT(b)
        }
        if self.is_known_true(b) {
            return -a; // a XOR true = NOT(a)
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
        self.add_clause(CnfClause::new(vec![-a, -b, -out]));
        self.add_clause(CnfClause::new(vec![-a, b, out]));
        self.add_clause(CnfClause::new(vec![a, -b, out]));
        self.add_clause(CnfClause::new(vec![a, b, -out]));

        // Cache the result
        self.xor_cache.insert(key, out);
        if self.capture_gate_provenance {
            self.xor_children.insert(out, key);
        }
        out
    }

    /// Create XNOR gate: out = a XNOR b = NOT(a XOR b)
    pub(super) fn mk_xnor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let xor = self.mk_xor(a, b);
        -xor
    }

    /// Create AND of many literals
    pub(super) fn mk_and_many(&mut self, lits: &[CnfLit]) -> CnfLit {
        if lits.is_empty() {
            return self.fresh_true();
        }
        if lits.len() == 1 {
            return lits[0];
        }

        let mut result = lits[0];
        for &lit in &lits[1..] {
            result = self.mk_and(result, lit);
        }
        result
    }

    /// Create MUX: if sel then a else b (bitwise)
    pub(super) fn bitwise_mux(&mut self, a: &BvBits, b: &BvBits, sel: CnfLit) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_mux(ai, bi, sel))
            .collect()
    }

    /// Create MUX: if sel then a else b
    ///
    /// Uses structural hashing to avoid duplicate MUX gates (#8143).
    /// Constant propagation: known selector, equal inputs, and known data
    /// inputs are resolved without allocating a fresh variable.
    pub(super) fn mk_mux(&mut self, a: CnfLit, b: CnfLit, sel: CnfLit) -> CnfLit {
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
        if a == -b {
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
            return self.mk_and(-sel, b);
        }
        if self.is_known_true(b) {
            return self.mk_or(-sel, a);
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
        self.add_clause(CnfClause::new(vec![-sel, -a, out]));
        self.add_clause(CnfClause::new(vec![-sel, a, -out]));
        self.add_clause(CnfClause::new(vec![sel, -b, out]));
        self.add_clause(CnfClause::new(vec![sel, b, -out]));

        // Cache the result
        self.mux_cache.insert(key, out);
        if self.capture_gate_provenance {
            self.mux_children.insert(out, key);
        }
        out
    }
}
