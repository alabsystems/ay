// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The length premise of an NF or flat-form alignment inference.
//!
//! N_UNIFY, F_UNIFY and ConstUnify each conclude an equality from TWO
//! premises: the alignment of two normal (or flat) forms, and a length fact,
//! `len(c1) = len(c2)` or `len(x) = n`. The solver reads the length fact from
//! the length terms' integer equivalence class (`are_lengths_equal_with_entail`,
//! `known_length_full`), and the alignment explanation does not cover it. An
//! inference that carries only the alignment learns `¬alignment ∨ c1 = c2`
//! for a length the SAT solver merely decided. When the alignment is an input
//! equality, that clause fixes `c1 = c2` under every length. This was a false
//! UNSAT on
//!
//! ```text
//! (assert (= (str.++ x "c" y) (str.++ "a" z "q")))
//! (assert (or (= (str.len x) 1) (= (str.len x) 4)))
//! (assert (str.in_re x (re.++ re.all (re.range "0" "9"))))
//! ```
//!
//! which `x = "aAB8"`, `y = "q"`, `z = "AB8c"` satisfies: the `len(x) = 1`
//! branch unified `x = "a"` with the input equality as its only reason, and
//! the membership conflict on `x = "a"` then refuted the input.
//!
//! Upstream 0eb3642a4 removed the same pattern from
//! `check_regex_length_disjoint`. These helpers apply its rule to the NF
//! inferences: the length comes with every literal behind it, from
//! `known_len_with_reasons` or `length_equality_reasons`, or the inference does
//! not fire.

use super::super::*;

impl CoreSolver {
    /// `reasons` extended with the length premise `premise`, without
    /// duplicates.
    pub(in super::super) fn with_length_premise(
        mut reasons: Vec<TheoryLit>,
        premise: Vec<TheoryLit>,
    ) -> Vec<TheoryLit> {
        let mut seen: HashSet<TheoryLit> = reasons.iter().copied().collect();
        Self::extend_dedup(&mut reasons, &mut seen, premise);
        reasons
    }

    /// The equal-length premise of a unify inference on `c1`, `c2`, with every
    /// literal behind it. `None` when `len(c1) = len(c2)` is not known, or is
    /// known only through facts the proof forest cannot explain (a pure
    /// `ArithEntail` bound): then the caller must not unify on it.
    pub(in super::super) fn unify_length_premise(
        terms: &TermStore,
        state: &SolverState,
        c1: TermId,
        c2: TermId,
    ) -> Option<Vec<TheoryLit>> {
        if !Self::are_lengths_equal_with_entail(terms, state, c1, c2) {
            return None;
        }
        Self::length_equality_reasons(terms, state, c1, c2)
    }

    /// ConstUnify (#4055): `x = y[start..end]` for the variable `x` aligned at
    /// offset `start` of the constant `y`, with `end - start` its known length.
    /// The lemma is guarded by the NF alignment (`nf_reasons`) AND by the
    /// literals behind that length (`len_premise`, from
    /// `known_len_with_reasons`): without the latter, backtracking the length
    /// decision leaves `x` pinned to this one slice.
    pub(in super::super) fn const_unify_lemma(
        x: TermId,
        y: TermId,
        start: usize,
        end: usize,
        nf_reasons: Vec<TheoryLit>,
        len_premise: Vec<TheoryLit>,
    ) -> NfCheckResult {
        NfCheckResult::NeedLemma(StringLemma {
            kind: StringLemmaKind::ConstUnify,
            x,
            y,
            char_offset: end,
            start_offset: start,
            reason: Self::with_length_premise(nf_reasons, len_premise),
        })
    }
}
