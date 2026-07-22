// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact decision procedure for single-equality 0/1 knapsacks
//! (`sum a_i x_i == b`), the Aardal_1 / cuww / prob DEC-LIN family.
//!
//! # Why this exists
//!
//! These instances encode one huge-coefficient equality over ~60-110 binary
//! variables (two complementary `>=` rows in normalized OPB). CDCL cutting
//! planes learns near-full-width saturated lemmas on them (measured: avg LBD
//! ~ decision depth, lemma width ~ variable count) and enumerates: at 30s the
//! whole family is UNKNOWN. But the family is trivially decidable EXACTLY by
//! subset-sum reachability: a bitset DP over `0..=b` with `reach |= reach <<
//! a_i` decides feasibility in `O(n * b / 64)` word operations — well under a
//! second for the competition family (`b <= ~9e7`, `n <= ~110`).
//!
//! # Soundness (fail-closed on every uncertain path)
//!
//! * **SAT**: the DP traceback produces a concrete assignment for the row
//!   variables. The caller re-verifies the full model against EVERY stored
//!   constraint row before accepting (and the binaries' decision-SAT
//!   self-check re-verifies again downstream). A failed verification declines
//!   (falls back to normal CDCL search) — a DP bug can therefore never emit a
//!   wrong SAT.
//! * **UNSAT**: reachability is computed twice — once in input item order and
//!   once in reversed order (different shift/word-boundary schedules). UNSAT
//!   is reported only when BOTH passes agree the target is unreachable;
//!   disagreement declines. The DP core is additionally differential-tested
//!   against brute-force enumeration (see tests).
//! * **Detection**: only exact structural matches are converted (one `Eq` row,
//!   or two `Ge` rows that are exact term-wise negations of each other, all
//!   terms linear, all arithmetic checked). Anything else declines.
//! * **Budget**: instances whose target or item count exceed the fixed
//!   memory/time budget decline. Interruption (should_stop) declines.
//!
//! Declining is always sound: the caller simply continues with the ordinary
//! CDCL search, exactly as if this module did not exist.

use std::collections::BTreeMap;

use crate::types::{PbConstraint, PbRel};

/// Largest supported equality target. `1 << 27` bits = 16 MiB per bitset;
/// the Aardal_1 family tops out near `9e7 < 2^27`.
const MAX_TARGET: u64 = 1 << 27;

/// Largest supported item (variable) count. The family is ~60-110 items; the
/// cap bounds the DP wall clock (`n` bitset shift-or passes plus one
/// checkpointed traceback) and total checkpoint memory.
const MAX_ITEMS: usize = 512;

/// Checkpoint interval for the traceback (a prefix bitset is retained every
/// this many items; each traceback segment recomputes at most this many).
const CHECKPOINT_INTERVAL: usize = 8;

/// Hard ceiling on the estimated peak allocation (checkpoints + one segment
/// of prefix bitsets + scratch). 384 MiB — comfortably inside competition
/// MEMLIMITs even with several portfolio workers resident.
const MEMORY_BUDGET_BYTES: u64 = 384 << 20;

/// One DP item: `coeff > 0` weight on binary variable `var`. `flipped` means
/// the ORIGINAL row variable enters the equality as `1 - x`, so the model
/// value for `var` is the NEGATION of the DP's "item used" bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EqItem {
    var: u32,
    coeff: u64,
    flipped: bool,
}

/// A detected single-equality 0/1 knapsack `sum coeff_i * y_i == target` with
/// all `coeff_i > 0` (negative-coefficient variables are complement-
/// substituted into `flipped` items during detection).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EqKnapsack {
    items: Vec<EqItem>,
    target: i128,
}

/// Outcome of the DP decision. `Inconclusive` is the fail-closed answer for
/// interrupts, budget refusals mid-flight, and any internal anomaly; the
/// caller must fall back to ordinary search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EqKnapsackOutcome {
    /// Feasible: `(var, value)` for every variable appearing in the equality.
    Sat(Vec<(u32, bool)>),
    /// The equality target is unreachable (confirmed by two independent
    /// forward passes).
    Unsat,
    /// No answer; caller falls back to normal search.
    Inconclusive,
}

impl EqKnapsack {
    /// Detects the single-equality knapsack pattern in a solving-instance row
    /// set. Accepts EXACTLY:
    /// * one linear `Eq` row, or
    /// * two linear `Ge` rows that are exact term-wise negations of each
    ///   other (`sum a x >= b` and `sum -a x >= -b`, i.e. `sum a x == b`).
    ///
    /// All arithmetic is checked; any overflow, duplicate-merge surprise, or
    /// structural mismatch returns `None` (decline).
    pub(crate) fn detect(rows: &[PbConstraint]) -> Option<Self> {
        let (coeffs, rhs) = match rows {
            [row] if row.rel == PbRel::Eq => canonicalize_row(row)?,
            [a, b] if a.rel == PbRel::Ge && b.rel == PbRel::Ge => {
                let (ca, ra) = canonicalize_row(a)?;
                let (cb, rb) = canonicalize_row(b)?;
                if ca.len() != cb.len() {
                    return None;
                }
                for (var, &coeff) in &ca {
                    if cb.get(var).copied()? != coeff.checked_neg()? {
                        return None;
                    }
                }
                if rb != ra.checked_neg()? {
                    return None;
                }
                (ca, ra)
            }
            _ => return None,
        };

        // Complement-substitute negative coefficients: `c*x` with `c < 0`
        // becomes `(-c)*(1-x) - (-c)`, i.e. a positive item on the flipped
        // variable with the target raised by `-c`.
        let mut items: Vec<EqItem> = Vec::with_capacity(coeffs.len());
        let mut target = rhs;
        for (var, coeff) in coeffs {
            debug_assert_ne!(coeff, 0, "canonicalize_row must drop zero terms");
            if coeff > 0 {
                items.push(EqItem {
                    var,
                    coeff: u64::try_from(coeff).ok()?,
                    flipped: false,
                });
            } else {
                let positive = coeff.checked_neg()?;
                target = target.checked_add(positive)?;
                items.push(EqItem {
                    var,
                    coeff: u64::try_from(positive).ok()?,
                    flipped: true,
                });
            }
        }

        // Orientation normalization: complementing EVERY item (`y -> 1-y`)
        // maps the target `t` to `total - t` with an identical solution set.
        // The complementary-Ge-pair form can be canonicalized from either
        // row, and the all-negative orientation yields `total - b` (which is
        // typically far larger than `b` and can blow the DP budget), so pick
        // the smaller of the two equivalent targets.
        let mut total: i128 = 0;
        for item in &items {
            total = total.checked_add(i128::from(item.coeff))?;
        }
        if target >= 0 && target <= total && target > total - target {
            for item in &mut items {
                item.flipped = !item.flipped;
            }
            target = total - target;
        }

        Some(Self { items, target })
    }

    /// Whether this knapsack fits the fixed memory/size budget. Out-of-range
    /// targets (`< 0` or `> sum of coefficients`) are trivially UNSAT and are
    /// always "within budget" (no bitset is allocated for them).
    pub(crate) fn within_budget(&self) -> bool {
        if self.items.len() > MAX_ITEMS {
            return false;
        }
        if self.trivially_unsat_target() {
            return true;
        }
        // items.len() <= MAX_ITEMS and target >= 0 here.
        let Ok(target) = u64::try_from(self.target) else {
            return false;
        };
        if target > MAX_TARGET {
            return false;
        }
        let words = target / 64 + 1;
        let bytes_per_bitset = words * 8;
        let checkpoints = (self.items.len() / CHECKPOINT_INTERVAL + 1) as u64;
        let segment = (CHECKPOINT_INTERVAL + 1) as u64;
        let estimated = bytes_per_bitset.saturating_mul(checkpoints + segment + 3);
        estimated <= MEMORY_BUDGET_BYTES
    }

    /// `true` when the target lies outside `[0, sum of coefficients]` — the
    /// equality is then unsatisfiable without any DP (the LHS range over all
    /// 0/1 assignments is exactly that interval).
    fn trivially_unsat_target(&self) -> bool {
        if self.target < 0 {
            return true;
        }
        let total: i128 = self.items.iter().map(|item| i128::from(item.coeff)).sum();
        self.target > total
    }

    /// Decides the equality. See the module docs for the soundness contract;
    /// every uncertain path returns [`EqKnapsackOutcome::Inconclusive`].
    pub(crate) fn solve<F>(&self, should_stop: &mut F) -> EqKnapsackOutcome
    where
        F: FnMut() -> bool + ?Sized,
    {
        if self.trivially_unsat_target() {
            return EqKnapsackOutcome::Unsat;
        }
        if !self.within_budget() {
            return EqKnapsackOutcome::Inconclusive;
        }
        // within_budget guarantees the conversion.
        let Ok(target) = u64::try_from(self.target) else {
            return EqKnapsackOutcome::Inconclusive;
        };

        // Forward pass in item order, retaining a checkpoint every
        // CHECKPOINT_INTERVAL items. checkpoints[j] = reachability using
        // items[0 .. j*CHECKPOINT_INTERVAL].
        let mut checkpoints: Vec<DpBits> =
            Vec::with_capacity(self.items.len() / CHECKPOINT_INTERVAL + 2);
        let mut reach = DpBits::new(target);
        for (i, item) in self.items.iter().enumerate() {
            if should_stop() {
                return EqKnapsackOutcome::Inconclusive;
            }
            if i % CHECKPOINT_INTERVAL == 0 {
                checkpoints.push(reach.clone());
            }
            reach.or_shifted_self(item.coeff);
        }

        if !reach.get(target) {
            // Confirm unreachability with an independent second pass in
            // REVERSED item order (subset-sum reachability is order-
            // independent, but the word/shift schedules differ, so a shift
            // or boundary bug is very unlikely to corrupt both passes the
            // same way). Disagreement declines — never guesses.
            let mut confirm = DpBits::new(target);
            for item in self.items.iter().rev() {
                if should_stop() {
                    return EqKnapsackOutcome::Inconclusive;
                }
                confirm.or_shifted_self(item.coeff);
            }
            if confirm.get(target) {
                return EqKnapsackOutcome::Inconclusive;
            }
            return EqKnapsackOutcome::Unsat;
        }

        // Reachable: trace an explicit witness back through the checkpoints.
        let Some(used) = self.traceback(target, &checkpoints, should_stop) else {
            return EqKnapsackOutcome::Inconclusive;
        };

        // Internal exact re-check of the witness against the equality (the
        // caller ALSO re-verifies against the actual constraint rows).
        let mut lhs: i128 = 0;
        for (item, &item_used) in self.items.iter().zip(&used) {
            if item_used {
                lhs += i128::from(item.coeff);
            }
        }
        if lhs != self.target {
            return EqKnapsackOutcome::Inconclusive;
        }

        let assignment = self
            .items
            .iter()
            .zip(&used)
            .map(|(item, &item_used)| (item.var, item_used != item.flipped))
            .collect();
        EqKnapsackOutcome::Sat(assignment)
    }

    /// Reconstructs one witness subset for a reachable `target`. Segment by
    /// segment (newest first) the prefix bitsets are recomputed from the
    /// nearest checkpoint, then items are decided right-to-left: an item is
    /// unused iff the remaining target is already reachable without it.
    /// Returns `None` on interrupt or any anomaly (fail closed).
    fn traceback<F>(
        &self,
        target: u64,
        checkpoints: &[DpBits],
        should_stop: &mut F,
    ) -> Option<Vec<bool>>
    where
        F: FnMut() -> bool + ?Sized,
    {
        let n = self.items.len();
        let mut used = vec![false; n];
        let mut t = target;

        for seg_idx in (0..checkpoints.len()).rev() {
            let seg_start = seg_idx * CHECKPOINT_INTERVAL;
            let seg_end = (seg_start + CHECKPOINT_INTERVAL).min(n);
            if seg_start >= n {
                continue;
            }

            // prefixes[k] = reachability using items[0 .. seg_start + k].
            let mut prefixes: Vec<DpBits> = Vec::with_capacity(seg_end - seg_start + 1);
            prefixes.push(checkpoints[seg_idx].clone());
            for item in &self.items[seg_start..seg_end] {
                if should_stop() {
                    return None;
                }
                let mut next = prefixes.last()?.clone();
                next.or_shifted_self(item.coeff);
                prefixes.push(next);
            }

            for i in (seg_start..seg_end).rev() {
                let without = &prefixes[i - seg_start];
                if without.get(t) {
                    // Reachable without item i: leave it unused.
                    continue;
                }
                // Item i must be used; the remainder must be reachable by
                // the strictly earlier prefix.
                let coeff = self.items[i].coeff;
                if t < coeff || !without.get(t - coeff) {
                    return None; // Anomaly: fail closed.
                }
                used[i] = true;
                t -= coeff;
            }
        }

        if t != 0 {
            return None; // Anomaly: fail closed.
        }
        Some(used)
    }
}

/// Canonicalizes one LINEAR row into `(var -> signed coefficient on the
/// positive literal, adjusted rhs)`: a term `c * ~x` is rewritten via
/// `~x = 1 - x` into coefficient `-c` on `x` with `c` moved to the rhs.
/// Duplicate variables are merged; zero coefficients dropped. Returns `None`
/// on any non-linear term or checked-arithmetic overflow.
fn canonicalize_row(row: &PbConstraint) -> Option<(BTreeMap<u32, i128>, i128)> {
    let mut coeffs: BTreeMap<u32, i128> = BTreeMap::new();
    let mut rhs = row.rhs;
    for term in &row.terms {
        let [lit] = term.lits.as_slice() else {
            return None; // Non-linear term: decline.
        };
        let (var, signed) = if lit.negated {
            rhs = rhs.checked_sub(term.coeff)?;
            (lit.var, term.coeff.checked_neg()?)
        } else {
            (lit.var, term.coeff)
        };
        let slot = coeffs.entry(var).or_insert(0);
        *slot = slot.checked_add(signed)?;
    }
    coeffs.retain(|_, c| *c != 0);
    Some((coeffs, rhs))
}

/// Growable-free fixed-width bitset for subset-sum reachability over
/// `0..=nbits_minus_one`. Bit `k` set means "sum `k` is reachable".
#[derive(Debug, Clone, PartialEq, Eq)]
struct DpBits {
    words: Vec<u64>,
    /// Highest representable bit index (the DP target).
    max_bit: u64,
}

impl DpBits {
    /// New bitset covering sums `0..=max_bit`, with only bit 0 (empty sum)
    /// set.
    fn new(max_bit: u64) -> Self {
        let words = vec![0u64; (max_bit / 64 + 1) as usize];
        let mut bits = Self { words, max_bit };
        bits.words[0] = 1;
        bits
    }

    /// `self |= self << shift`, truncated to `max_bit`. A shift beyond
    /// `max_bit` is a no-op (those sums are unrepresentable and irrelevant).
    fn or_shifted_self(&mut self, shift: u64) {
        if shift == 0 || shift > self.max_bit {
            return;
        }
        let word_shift = (shift / 64) as usize;
        let bit_shift = shift % 64;
        let len = self.words.len();
        if bit_shift == 0 {
            for i in (word_shift..len).rev() {
                self.words[i] |= self.words[i - word_shift];
            }
        } else {
            for i in (word_shift..len).rev() {
                let mut v = self.words[i - word_shift] << bit_shift;
                if i > word_shift {
                    v |= self.words[i - word_shift - 1] >> (64 - bit_shift);
                }
                self.words[i] |= v;
            }
        }
        // Clear bits beyond max_bit so `get` and equality stay canonical.
        let top_used = (self.max_bit % 64) as u32;
        if top_used < 63 {
            let mask = (1u64 << (top_used + 1)) - 1;
            let last = self.words.len() - 1;
            self.words[last] &= mask;
        }
    }

    /// Whether sum `bit` is reachable. Out-of-range queries return `false`.
    fn get(&self, bit: u64) -> bool {
        if bit > self.max_bit {
            return false;
        }
        (self.words[(bit / 64) as usize] >> (bit % 64)) & 1 == 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn not(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn ge_row(terms: &[(i128, PbLit)], rhs: i128) -> PbConstraint {
        PbConstraint {
            terms: terms
                .iter()
                .map(|&(coeff, l)| PbTerm {
                    coeff,
                    lits: vec![l],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq_row(terms: &[(i128, PbLit)], rhs: i128) -> PbConstraint {
        PbConstraint {
            rel: PbRel::Eq,
            ..ge_row(terms, rhs)
        }
    }

    fn never_stop() -> impl FnMut() -> bool {
        || false
    }

    #[test]
    fn detects_eq_row() {
        // total = 15, raw target 8: orientation normalization flips every
        // item to the equivalent complement problem with target 7.
        let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 8)];
        let knap = EqKnapsack::detect(&rows).expect("must detect single Eq row");
        assert_eq!(knap.target, 7);
        assert_eq!(knap.items.len(), 3);
        assert!(knap.items.iter().all(|i| i.flipped));

        // A below-half target keeps the plain orientation.
        let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 7)];
        let knap = EqKnapsack::detect(&rows).expect("must detect single Eq row");
        assert_eq!(knap.target, 7);
        assert!(knap.items.iter().all(|i| !i.flipped));
    }

    #[test]
    fn detects_complementary_ge_pair() {
        let rows = [
            ge_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 8),
            ge_row(&[(-3, lit(1)), (-5, lit(2)), (-7, lit(3))], -8),
        ];
        let knap = EqKnapsack::detect(&rows).expect("must detect complementary Ge pair");
        // Orientation-normalized: min(8, 15-8) = 7.
        assert_eq!(knap.target, 7);
        assert_eq!(knap.items.len(), 3);
    }

    #[test]
    fn detects_pair_in_either_order() {
        let rows = [
            ge_row(&[(-3, lit(1)), (-5, lit(2))], -5),
            ge_row(&[(3, lit(1)), (5, lit(2))], 5),
        ];
        assert!(EqKnapsack::detect(&rows).is_some());
    }

    #[test]
    fn detects_negated_literal_form() {
        // 3*~x1 + 5*x2 == 5  ->  -3*x1 + 5*x2 == 2  ->  flipped item on x1,
        // raw target 2 + 3 = 5; total = 8, so orientation normalization
        // complements both items down to target 3.
        let rows = [eq_row(&[(3, not(1)), (5, lit(2))], 5)];
        let knap = EqKnapsack::detect(&rows).expect("negated literals must canonicalize");
        assert_eq!(knap.target, 3);
        let flipped: Vec<bool> = knap.items.iter().map(|i| i.flipped).collect();
        assert_eq!(flipped, vec![false, true]);
    }

    #[test]
    fn declines_non_complementary_pair() {
        let rows = [
            ge_row(&[(3, lit(1)), (5, lit(2))], 4),
            ge_row(&[(-3, lit(1)), (-5, lit(2))], -5),
        ];
        assert!(EqKnapsack::detect(&rows).is_none());
    }

    #[test]
    fn declines_mismatched_vars() {
        let rows = [
            ge_row(&[(3, lit(1)), (5, lit(2))], 4),
            ge_row(&[(-3, lit(1)), (-5, lit(3))], -4),
        ];
        assert!(EqKnapsack::detect(&rows).is_none());
    }

    #[test]
    fn declines_single_ge_row() {
        let rows = [ge_row(&[(3, lit(1)), (5, lit(2))], 4)];
        assert!(EqKnapsack::detect(&rows).is_none());
    }

    #[test]
    fn declines_nonlinear_term() {
        let mut row = eq_row(&[(3, lit(1))], 3);
        row.terms.push(PbTerm {
            coeff: 2,
            lits: vec![lit(2), lit(3)],
        });
        assert!(EqKnapsack::detect(&[row]).is_none());
    }

    #[test]
    fn merges_duplicate_vars() {
        // 3*x1 + 2*x1 == 5 -> single item coeff 5.
        let rows = [eq_row(&[(3, lit(1)), (2, lit(1))], 5)];
        let knap = EqKnapsack::detect(&rows).expect("duplicates must merge");
        assert_eq!(knap.items.len(), 1);
        assert_eq!(knap.items[0].coeff, 5);
    }

    #[test]
    fn cancelled_duplicate_drops_to_zero_coeff() {
        // 3*x1 - 3*x1 + 5*x2 == 5 -> x1 vanishes.
        let rows = [eq_row(&[(3, lit(1)), (-3, lit(1)), (5, lit(2))], 5)];
        let knap = EqKnapsack::detect(&rows).expect("cancelled var must drop");
        assert_eq!(knap.items.len(), 1);
        assert_eq!(knap.items[0].var, 2);
    }

    #[test]
    fn solve_sat_finds_witness() {
        let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 10)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        match knap.solve(&mut never_stop()) {
            EqKnapsackOutcome::Sat(assignment) => {
                let sum: i128 = assignment
                    .iter()
                    .map(|&(var, val)| match (var, val) {
                        (1, true) => 3,
                        (2, true) => 5,
                        (3, true) => 7,
                        _ => 0,
                    })
                    .sum();
                assert_eq!(sum, 10, "witness must satisfy the equality");
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn solve_unsat_when_unreachable() {
        // 3, 5, 7: cannot make 4.
        let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 4)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
    }

    #[test]
    fn solve_unsat_target_out_of_range() {
        let rows = [eq_row(&[(3, lit(1))], 100)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);

        let rows = [eq_row(&[(3, lit(1))], -1)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
    }

    #[test]
    fn solve_with_flipped_items() {
        // 4*~x1 + 6*x2 == 4: x1 false, x2 false — or x1 true impossible
        // (target would need 0 or 6 from x2 alone: 4-... ). Enumerate:
        // x1=F,x2=F -> 4. SAT with x1 false.
        let rows = [eq_row(&[(4, not(1)), (6, lit(2))], 4)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        match knap.solve(&mut never_stop()) {
            EqKnapsackOutcome::Sat(assignment) => {
                let val = |v: u32| assignment.iter().find(|(var, _)| *var == v).unwrap().1;
                let lhs = 4 * i128::from(!val(1)) + 6 * i128::from(val(2));
                assert_eq!(lhs, 4);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn interrupt_is_inconclusive() {
        let rows = [eq_row(&[(3, lit(1)), (5, lit(2)), (7, lit(3))], 10)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        let mut always_stop = || true;
        assert_eq!(
            knap.solve(&mut always_stop),
            EqKnapsackOutcome::Inconclusive
        );
    }

    #[test]
    fn budget_declines_oversized_target() {
        // Both orientations exceed MAX_TARGET (total = 2*(MAX+5), target =
        // MAX+5 in either orientation), so the budget must decline.
        let big = i128::from(MAX_TARGET) + 5;
        let rows = [eq_row(&[(big, lit(1)), (big, lit(2))], big)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert!(!knap.within_budget());
    }

    #[test]
    fn orientation_normalization_rescues_oversized_raw_target() {
        // Raw target MAX+5 exceeds the cap, but the complement target is 0,
        // so normalization keeps the instance solvable in budget.
        let big = i128::from(MAX_TARGET) + 5;
        let rows = [eq_row(&[(big, lit(1))], big)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert!(knap.within_budget());
        match knap.solve(&mut never_stop()) {
            EqKnapsackOutcome::Sat(assignment) => {
                assert_eq!(assignment, vec![(1, true)]);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn budget_accepts_trivially_unsat_huge_target() {
        // Out-of-range target never allocates, so it is always in budget and
        // resolves Unsat immediately.
        let rows = [eq_row(&[(3, lit(1))], i128::MAX / 2)];
        let knap = EqKnapsack::detect(&rows).unwrap();
        assert!(knap.within_budget());
        assert_eq!(knap.solve(&mut never_stop()), EqKnapsackOutcome::Unsat);
    }

    /// Deterministic xorshift for the differential test (no external deps).
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound.max(1)
        }
    }

    /// Brute-force subset-sum ground truth: which assignments of the original
    /// row variables satisfy the equality.
    fn brute_force_sat(knap: &EqKnapsack) -> bool {
        let n = knap.items.len();
        for mask in 0u64..(1u64 << n) {
            let mut lhs: i128 = 0;
            for (i, item) in knap.items.iter().enumerate() {
                if (mask >> i) & 1 == 1 {
                    lhs += i128::from(item.coeff);
                }
            }
            if lhs == knap.target {
                return true;
            }
        }
        false
    }

    /// DIFFERENTIAL GATE: the DP verdict must match brute-force enumeration
    /// on thousands of random small equality knapsacks, and every SAT witness
    /// must satisfy the equality exactly. This is the trust anchor for the
    /// UNSAT path (which has no runtime witness).
    #[test]
    fn differential_dp_vs_brute_force() {
        let mut rng = XorShift(0x5eed_cafe_f00d_1234);
        for round in 0..4000 {
            let n = 1 + (rng.below(11) as usize); // 1..=11 items
            let mut terms = Vec::with_capacity(n);
            let mut total: i128 = 0;
            for v in 0..n {
                let coeff = 1 + rng.below(60) as i128;
                total += coeff;
                // Mix in negated literals and negative coefficients to
                // exercise canonicalization + flipping.
                let negate_lit = rng.below(4) == 0;
                let negate_coeff = rng.below(4) == 0;
                let l = if negate_lit {
                    not(v as u32 + 1)
                } else {
                    lit(v as u32 + 1)
                };
                terms.push((if negate_coeff { -coeff } else { coeff }, l));
            }
            // Target from slightly beyond the raw range so infeasible cases
            // (incl. out-of-range) are common.
            let raw_target = rng.below((2 * total + 20) as u64) as i128 - total / 2;
            let row = eq_row(&terms, raw_target);
            let Some(knap) = EqKnapsack::detect(&[row]) else {
                panic!("round {round}: detection must succeed on a linear Eq row");
            };
            let expected = brute_force_sat(&knap);
            match knap.solve(&mut never_stop()) {
                EqKnapsackOutcome::Sat(assignment) => {
                    assert!(
                        expected,
                        "round {round}: DP said SAT, brute force says UNSAT"
                    );
                    // Witness must satisfy the equality on ORIGINAL vars.
                    let lhs: i128 = knap
                        .items
                        .iter()
                        .map(|item| {
                            let value = assignment
                                .iter()
                                .find(|(var, _)| *var == item.var)
                                .expect("assignment covers every item var")
                                .1;
                            let used = value != item.flipped;
                            if used {
                                i128::from(item.coeff)
                            } else {
                                0
                            }
                        })
                        .sum();
                    assert_eq!(lhs, knap.target, "round {round}: witness violates equality");
                }
                EqKnapsackOutcome::Unsat => {
                    assert!(
                        !expected,
                        "round {round}: DP said UNSAT, brute force says SAT"
                    );
                }
                EqKnapsackOutcome::Inconclusive => {
                    panic!("round {round}: uninterrupted in-budget solve must be conclusive");
                }
            }
        }
    }

    /// The Ge-pair form must decide identically to the equivalent Eq row.
    #[test]
    fn differential_pair_vs_eq_row() {
        let mut rng = XorShift(0xabcd_ef01_2345_6789);
        for _ in 0..500 {
            let n = 1 + (rng.below(8) as usize);
            let mut terms = Vec::with_capacity(n);
            for v in 0..n {
                terms.push((1 + rng.below(40) as i128, lit(v as u32 + 1)));
            }
            let total: i128 = terms.iter().map(|(c, _)| *c).sum();
            let target = rng.below((total + 1) as u64) as i128;
            let neg_terms: Vec<(i128, PbLit)> = terms.iter().map(|&(c, l)| (-c, l)).collect();
            let eq = [eq_row(&terms, target)];
            let pair = [ge_row(&terms, target), ge_row(&neg_terms, -target)];
            let a = EqKnapsack::detect(&eq).unwrap().solve(&mut never_stop());
            let b = EqKnapsack::detect(&pair).unwrap().solve(&mut never_stop());
            match (&a, &b) {
                (EqKnapsackOutcome::Sat(_), EqKnapsackOutcome::Sat(_)) => {}
                (EqKnapsackOutcome::Unsat, EqKnapsackOutcome::Unsat) => {}
                other => panic!("Eq row and Ge pair disagree: {other:?}"),
            }
        }
    }

    #[test]
    fn dpbits_shift_boundaries() {
        // Exercise word-boundary shifts explicitly.
        for &shift in &[1u64, 63, 64, 65, 127, 128, 129] {
            let mut bits = DpBits::new(300);
            bits.or_shifted_self(shift);
            assert!(bits.get(0));
            assert!(bits.get(shift), "bit {shift} must be reachable");
            bits.or_shifted_self(shift);
            assert!(bits.get(2 * shift), "bit {} must be reachable", 2 * shift);
            // Only {0, shift, 2*shift} are reachable; probe a non-member.
            assert!(!bits.get(2 * shift + 1));
        }
        // Shift beyond max_bit is a no-op.
        let mut bits = DpBits::new(10);
        bits.or_shifted_self(11);
        assert_eq!(bits.words[0], 1);
    }
}
