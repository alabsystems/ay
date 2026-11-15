// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simulation signatures that counterexamples keep refining.
//!
//! A gate's signature is its PHASE (its value under the very first pattern),
//! a hash of every phase-normalized simulation word so far, and whether any of
//! those words was nonzero. Two gates share a candidate class exactly when
//! every word agrees up to phase — modulo a 64-bit hash collision, which only
//! costs one refuted candidate, never a wrong merge: every merge is proved.
//!
//! The sweep used to keep the words themselves and stop refining at 64 of
//! them. Measured 2026-09-30 on external-codegen's 64-bit `SDIV` definitional rows
//! (264,472 gates): the 64 words were spent while thousands of carry chains
//! of different lengths — `x >= 1` over every suffix of the dividend, one per
//! divider level and bit — still shared one class, every later chain gate paid
//! a refuted SAT call per member, and the sweep ran out of lemma calls half way
//! through the circuit. A hash per gate costs the same memory at any number of
//! words, so the classes keep splitting for as long as models arrive.

use super::splitmix;

pub(super) struct Signatures {
    phase: Vec<bool>,
    hash: Vec<u64>,
    varies: Vec<bool>,
    words: usize,
    /// Whether the phases are read (from the first pattern that counts).
    phased: bool,
}

impl Signatures {
    pub(super) fn new(count: usize) -> Self {
        Self {
            phase: vec![false; count],
            hash: vec![0; count],
            varies: vec![false; count],
            words: 0,
            phased: false,
        }
    }

    /// Fold one simulation word (`values[var]`, 64 patterns) into every
    /// gate's signature, reading only the patterns set in `care` (all of
    /// them outside a sweep under hypotheses, `care.rs`). A gate's phase is
    /// its value under the first pattern read.
    pub(super) fn absorb(&mut self, values: &[u64], care: u64) {
        self.words += 1;
        if care == 0 {
            return;
        }
        let lane = care.trailing_zeros();
        let first = !std::mem::replace(&mut self.phased, true);
        for (var, &value) in values.iter().enumerate().take(self.hash.len()) {
            if first {
                self.phase[var] = (value >> lane) & 1 == 1;
            }
            let normalized = if self.phase[var] { !value } else { value } & care;
            self.varies[var] |= normalized != 0;
            self.hash[var] = splitmix(self.hash[var] ^ normalized);
        }
    }

    /// Words absorbed so far.
    pub(super) fn words(&self) -> usize {
        self.words
    }

    /// `var`'s class key and phase, and whether every pattern so far gave it
    /// the value of its phase (a candidate constant).
    pub(super) fn of(&self, var: usize) -> (u64, bool, bool) {
        (self.hash[var], self.phase[var], !self.varies[var])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complementary_gates_share_a_class_and_a_constant_is_recognized() {
        let mut signatures = Signatures::new(3);
        signatures.absorb(&[0b1010, !0b1010, 0], u64::MAX);
        signatures.absorb(&[0b0110, !0b0110, 0], u64::MAX);
        let (a, a_phase, a_constant) = signatures.of(0);
        let (b, b_phase, b_constant) = signatures.of(1);
        let (_, _, c_constant) = signatures.of(2);
        assert_eq!(a, b);
        assert_ne!(a_phase, b_phase);
        assert!(!a_constant && !b_constant && c_constant);
        assert_eq!(signatures.words(), 2);
    }

    #[test]
    fn one_differing_word_splits_a_class() {
        let mut signatures = Signatures::new(2);
        signatures.absorb(&[0b1000, 0b1000], u64::MAX);
        assert_eq!(signatures.of(0).0, signatures.of(1).0);
        signatures.absorb(&[0b1, 0b0], u64::MAX);
        assert_ne!(signatures.of(0).0, signatures.of(1).0);
    }

    /// Patterns outside `care` are never read: two gates that differ only
    /// there share a class, and one that is constant there is a candidate
    /// constant.
    #[test]
    fn only_the_cared_for_patterns_are_read() {
        let mut signatures = Signatures::new(3);
        signatures.absorb(&[0b0110, 0b1110, 0b1001], 0b0110);
        signatures.absorb(&[0, 0b1, 0b1000], 0b0110);
        assert_eq!(signatures.of(0).0, signatures.of(1).0);
        assert!(!signatures.of(0).2);
        // Gate 2 reads 0 on both cared-for patterns of both words.
        assert!(signatures.of(2).2);
        assert_eq!(signatures.words(), 2);
    }
}
