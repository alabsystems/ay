// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod bound_propagations;
mod direct_bound_propagations;
pub(crate) mod jit_compile;
pub(crate) mod jit_update_contract;
mod solver_hooks;
mod var_atoms;

impl LraSolver {
    /// Integer-gap tautology test for the clause `(x ≤/< upper) ∨ (x ≥/> lower)`
    /// over an integer-valued variable (seed-981 false UNSAT).
    ///
    /// The clause is a tautology over the integers iff no integer violates
    /// BOTH bounds. An integer `z` violates the upper bound iff `z > upper`
    /// (non-strict) or `z >= upper` (strict); it violates the lower bound iff
    /// `z < lower` (non-strict) or `z <= lower` (strict). So the clause is a
    /// tautology iff
    ///   smallest integer violating upper  >  largest integer violating lower.
    ///
    /// The previous check (`upper == lower - 1`) is only correct when both
    /// bound values are integers: for `upper = -5/3`, `lower = -2/3` it
    /// claimed `(x <= -5/3) ∨ (x >= -2/3)` was a tautology, excluding the
    /// integer `x = -1` that sits in the open gap — an unsound axiom that
    /// produced a false UNSAT when injected without validation (seed 981).
    fn integer_bound_clause_is_tautology(
        upper_value: &Rational,
        upper_strict: bool,
        lower_value: &Rational,
        lower_strict: bool,
    ) -> bool {
        // Smallest integer violating the upper bound.
        let lo_violating_upper = if upper_strict {
            // x < k violated by z >= k: smallest is ceil(k).
            upper_value.ceil()
        } else {
            // x <= k violated by z > k: smallest is floor(k) + 1.
            upper_value.floor() + 1
        };
        // Largest integer violating the lower bound.
        let hi_violating_lower = if lower_strict {
            // x > k violated by z <= k: largest is floor(k).
            lower_value.floor()
        } else {
            // x >= k violated by z < k: largest is ceil(k) - 1.
            lower_value.ceil() - 1
        };
        lo_violating_upper > hi_violating_lower
    }

    /// Generate a binary axiom clause for a pair of bound atoms.
    /// Implements Z3's `mk_bound_axiom` 8-case logic.
    /// Reference: `reference/z3/src/sat/smt/arith_axioms.cpp:458-510`.
    // #8529: Use deterministic HashSet type (module-level import) for
    // axiom dedup to ensure consistent behavior across process runs.
    pub(crate) fn mk_bound_axiom_terms(
        &self,
        b1: &AtomRef,
        b2: &AtomRef,
        out: &mut Vec<(TermId, bool, TermId, bool)>,
        seen: &mut HashSet<(TermId, TermId)>,
    ) {
        let (t1, t2) = (b1.term, b2.term);
        let (k1, k2) = (&b1.bound_value, &b2.bound_value);
        if k1 == k2 && b1.is_upper == b2.is_upper && b1.strict == b2.strict {
            return;
        }
        // Dedup: normalize pair order so (a,b) == (b,a)
        let key = if t1 <= t2 { (t1, t2) } else { (t2, t1) };
        if !seen.insert(key) {
            return;
        }

        // Helper: for lower bounds, "strictly stronger" means higher value or
        // same value but strict. For upper bounds, "strictly stronger" means
        // lower value or same value but strict.
        //
        // b1_implies_b2 means: if b1 holds then b2 holds.
        // For lower bounds: b1 implies b2 when b1's effective lower bound is
        // at least as tight as b2's.
        //   x >= k1 implies x >= k2 when k1 >= k2 (but NOT when k1==k2 and b1 is non-strict, b2 is strict)
        //   x > k1  implies x >= k2 when k1 >= k2
        //   x >= k1 implies x > k2  only when k1 > k2 (NOT k1 == k2)
        //   x > k1  implies x > k2  when k1 >= k2

        if !b1.is_upper {
            // b1 is lower bound
            if !b2.is_upper {
                // Both lower: check if b1 implies b2 (#6242 strictness fix).
                // b1 implies b2 iff every x satisfying b1 also satisfies b2.
                //   k1 > k2: always (regardless of strictness)
                //   k1 == k2, b2 non-strict: always (non-strict is weaker)
                //   k1 == k2, b2 strict, b1 strict: yes
                //   k1 == k2, b2 strict, b1 non-strict: NO (x=k satisfies b1 not b2)
                let b1_implies_b2 = *k1 > *k2 || (*k1 == *k2 && (!b2.strict || b1.strict));
                let b2_implies_b1 = *k2 > *k1 || (*k2 == *k1 && (!b1.strict || b2.strict));
                if b1_implies_b2 {
                    out.push((t1, false, t2, true)); // ~l1 ∨ l2
                } else if b2_implies_b1 {
                    out.push((t1, true, t2, false)); // l1 ∨ ~l2
                }
                // When neither implies the other (k1==k2, one strict one not,
                // and the strict one doesn't imply the non-strict), we cannot
                // emit a sound axiom. This case is handled above: if k1==k2 and
                // b2.strict && !b1.strict, b1_implies_b2 is false and
                // b2_implies_b1 is true (x > k implies x >= k).
            } else {
                // b1 lower, b2 upper
                // Tautology: l1 ∨ l2 iff every x satisfies b1 OR b2.
                //   (x >= k1) ∨ (x <= k2) is tautology when k1 <= k2
                //   (x > k1) ∨ (x < k2) is tautology when k1 < k2
                //   At k1==k2: (x >= k) ∨ (x <= k) = tautology
                //              (x > k) ∨ (x <= k) = tautology
                //              (x >= k) ∨ (x < k) = tautology
                //              (x > k) ∨ (x < k) = NOT tautology (x=k fails)
                let is_tautology = *k1 < *k2 || (*k1 == *k2 && (!b1.strict || !b2.strict));
                if is_tautology {
                    out.push((t1, true, t2, true)); // l1 ∨ l2 (tautology aids BCP)
                } else {
                    // Conflict exclusion: ~l1 ∨ ~l2 iff b1 and b2 cannot both hold.
                    //   (x >= k1) ∧ (x <= k2) is empty when k1 > k2
                    //   (x > k1) ∧ (x < k2) is empty when k1 >= k2
                    //   At k1==k2 with both strict: (x > k) ∧ (x < k) = empty
                    let is_conflict = *k1 > *k2 || (*k1 == *k2 && b1.strict && b2.strict);
                    if is_conflict {
                        out.push((t1, false, t2, false)); // ~l1 ∨ ~l2
                    }
                    // Integer trichotomy: b1 is the lower bound, b2 the upper.
                    // Sound iff no integer violates both bounds (seed-981).
                    if self.integer_mode
                        && Self::integer_bound_clause_is_tautology(k2, b2.strict, k1, b1.strict)
                    {
                        out.push((t1, true, t2, true)); // integer trichotomy
                    }
                }
            }
        } else {
            // b1 is upper bound (x <= k1 when true, or x < k1 if strict)
            if !b2.is_upper {
                // b1 upper, b2 lower — symmetric to (b2 lower, b1 upper)
                let is_tautology = *k1 > *k2 || (*k1 == *k2 && (!b1.strict || !b2.strict));
                if is_tautology {
                    out.push((t1, true, t2, true)); // l1 ∨ l2 (tautology aids BCP)
                } else {
                    let is_conflict = *k1 < *k2 || (*k1 == *k2 && b1.strict && b2.strict);
                    if is_conflict {
                        out.push((t1, false, t2, false)); // ~l1 ∨ ~l2
                    }
                    // Integer trichotomy: b1 is the upper bound, b2 the lower.
                    // Sound iff no integer violates both bounds (seed-981).
                    if self.integer_mode
                        && Self::integer_bound_clause_is_tautology(k1, b1.strict, k2, b2.strict)
                    {
                        out.push((t1, true, t2, true)); // integer trichotomy
                    }
                }
            } else {
                // Both upper: b2 implies b1 iff every x satisfying b2 also satisfies b1.
                //   k1 > k2: always
                //   k1 == k2, b1 non-strict: always (non-strict is weaker)
                //   k1 == k2, b1 strict, b2 strict: yes
                //   k1 == k2, b1 strict, b2 non-strict: NO
                let b2_implies_b1 = *k1 > *k2 || (*k1 == *k2 && (!b1.strict || b2.strict));
                let b1_implies_b2 = *k2 > *k1 || (*k2 == *k1 && (!b2.strict || b1.strict));
                if b2_implies_b1 {
                    out.push((t1, true, t2, false)); // l1 ∨ ~l2 (b2 → b1)
                } else if b1_implies_b2 {
                    out.push((t1, false, t2, true)); // ~l1 ∨ l2 (b1 → b2)
                }
            }
        }
    }
}
