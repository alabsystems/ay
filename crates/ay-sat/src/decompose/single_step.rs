// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The single-step guard on the representative map.

use crate::literal::Literal;

use super::{Decompose, DecomposeResult};

impl Decompose {
    /// Second guard behind the live-only [`super::BinaryGraph`]: every literal
    /// must map straight to a representative that maps to itself, before
    /// anything is rewritten.
    ///
    /// One Tarjan pass over a skew-symmetric implication graph never maps a
    /// literal to a substituted literal. A graph that is not skew-symmetric
    /// can: an SCC and its mirror hold different variables, and each picks its
    /// own representative. On SAT-COMP 5314fd6c (2026-09-14) that chained 7
    /// variables, for example 193420 -> 193419 -> 193374. The rewrite then left
    /// clauses on the substituted 193419, and the reconstruction replayed
    /// `193420 := 193419` before `193419 := 193374`, so the model broke an
    /// original clause.
    ///
    /// Every link is an equivalence proved by live binaries, so the composed map
    /// is sound, and a DRAT or VeriPB rewrite stays RUP through the same
    /// binaries. The LRAT chains cover one link only, so under LRAT a chain
    /// refuses the round instead. A cycle, or a composed map that is not
    /// consistent across polarities, refuses it in every mode.
    pub(super) fn make_representatives_single_step(
        &mut self,
        num_lits: usize,
        need_chains: bool,
        result: &mut DecomposeResult,
    ) {
        let mut single: Vec<Literal> = Vec::with_capacity(num_lits);
        let mut chained = 0u64;
        let mut sound = true;
        for li in 0..num_lits {
            let first = self.reprs[li];
            let mut repr = first;
            let mut steps = 0usize;
            while self.reprs[repr.index()] != repr {
                repr = self.reprs[repr.index()];
                steps += 1;
                if steps > num_lits {
                    sound = false;
                    break;
                }
            }
            if !sound {
                break;
            }
            chained += u64::from(repr != first);
            single.push(repr);
        }
        if sound && chained > 0 {
            sound = !need_chains && (0..num_lits).all(|li| single[li ^ 1] == single[li].negated());
        }
        if !sound {
            self.stats.chained_rounds_refused += 1;
            for (i, repr) in self.reprs[..num_lits].iter_mut().enumerate() {
                *repr = Literal(i as u32);
            }
            result.substituted = 0;
            for chain in &mut result.equiv_chains {
                chain.repr_to_lit.clear();
                chain.lit_to_repr.clear();
            }
            return;
        }
        if chained > 0 {
            self.stats.chained_representatives += chained;
            self.reprs[..num_lits].copy_from_slice(&single);
        }
    }
}
