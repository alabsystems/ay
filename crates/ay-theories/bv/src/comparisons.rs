// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-blasting for BV comparison operations.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast equality: a = b
    pub(crate) fn bitblast_eq(&mut self, a: &BvBits, b: &BvBits) -> CnfLit {
        assert_eq!(a.len(), b.len());

        // a = b iff all bits are equal
        // Each bit equal: (ai XOR bi) = false, i.e., ~(ai XOR bi)
        let mut equal_bits: Vec<CnfLit> = Vec::new();
        for (&ai, &bi) in a.iter().zip(b.iter()) {
            let xor = self.mk_xor(ai, bi);
            equal_bits.push(-xor); // NOT XOR = XNOR = equal
        }

        // AND all equalities
        self.mk_and_many(&equal_bits)
    }

    /// Bit-blast unsigned less-than: a < b
    pub(crate) fn bitblast_ult(&mut self, a: &BvBits, b: &BvBits) -> CnfLit {
        assert_eq!(a.len(), b.len());
        let n = a.len();

        if n == 0 {
            return self.fresh_false();
        }

        // a < b from MSB to LSB
        // Starting from MSB, find first bit where they differ
        // If a[i] < b[i] (i.e., a[i]=0, b[i]=1), then a < b

        // Build from LSB to MSB
        // lt[i] = (a[i] < b[i]) OR ((a[i] = b[i]) AND lt[i-1])
        //
        // Initialize lt to known-false so gate constant propagation eliminates
        // the first iteration's intermediate variables: mk_and(eq, false) = false,
        // mk_or(a_lt_b, false) = a_lt_b, avoiding 2 extra variables + 5 clauses.
        let mut lt = self.fresh_false();

        for i in 0..n {
            let ai = a[i];
            let bi = b[i];

            // a[i] < b[i] means a[i]=0 and b[i]=1
            let a_lt_b = self.mk_and(-ai, bi);

            // a[i] = b[i] means XNOR
            let xor = self.mk_xor(ai, bi);
            let eq = -xor;

            // New lt = a_lt_b OR (eq AND old_lt)
            let eq_and_lt = self.mk_and(eq, lt);
            lt = self.mk_or(a_lt_b, eq_and_lt);
        }

        lt
    }

    /// Bit-blast unsigned less-or-equal: a <= b
    pub(crate) fn bitblast_ule(&mut self, a: &BvBits, b: &BvBits) -> CnfLit {
        // a <= b iff NOT (b < a)
        let b_lt_a = self.bitblast_ult(b, a);
        -b_lt_a
    }

    /// Bit-blast signed less-than: a <_s b
    pub(crate) fn bitblast_slt(&mut self, a: &BvBits, b: &BvBits) -> CnfLit {
        assert_eq!(a.len(), b.len());
        let n = a.len();

        if n == 0 {
            return self.fresh_false();
        }

        let sign_a = a[n - 1];
        let sign_b = b[n - 1];

        // Case 1: a negative, b non-negative => a < b
        let a_neg_b_pos = self.mk_and(sign_a, -sign_b);

        // Case 2: signs equal, compare magnitudes
        let signs_eq = self.mk_xnor(sign_a, sign_b);
        let ult = self.bitblast_ult(a, b);
        let same_sign_lt = self.mk_and(signs_eq, ult);

        self.mk_or(a_neg_b_pos, same_sign_lt)
    }

    /// Bit-blast signed less-or-equal: a <=_s b
    pub(crate) fn bitblast_sle(&mut self, a: &BvBits, b: &BvBits) -> CnfLit {
        let b_lt_a = self.bitblast_slt(b, a);
        -b_lt_a
    }
}
