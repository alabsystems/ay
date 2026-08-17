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
mod tests;
