// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict explanation: turning an empty feasible set into a learned clause.
//!
//! # The setting
//!
//! An MCSAT search assigns variables one at a time. At some point the feasible
//! set for the next variable `x_k` becomes EMPTY: the sign conditions on the
//! trail, together with the assignment to `x_1..x_{k-1}`, admit no value for
//! `x_k`. Explanation turns that dead end into a CLAUSE that is valid in the
//! theory and false under the current assignment, so the search can backjump
//! and never revisit it.
//!
//! # The port target is not readable here
//!
//! The reference named for this work is z3's `src/nlsat/nlsat_explain.cpp`.
//! `reference/z3/` in this tree is a BINARY distribution — `bin/` (compiled
//! `libz3.a`, `libz3.dylib`, a jar, a `.dll`) and `include/` (14 C/C++ API
//! headers) — with **zero `.cpp` files** and zero files whose name contains
//! `nlsat`. `grep -ril nlsat include/` matches only `z3_api.h` and `z3++.h`,
//! and the matches there are the substring `explain` in unrelated doc comments,
//! not the module. So no line count, structural correspondence or fidelity
//! claim is made against that file: it was never read. What is implemented here
//! is the published algorithm (Jovanovic & de Moura, "Solving Non-Linear
//! Arithmetic", IJCAR 2012, §4) and the CAD projection semantics it cites.
//!
//! # Priority order, and why the checker exists before the producer
//!
//! **An explanation that is not implied is a wrong `unsat` waiting to happen.**
//! A learned clause that is not a theory consequence prunes away satisfying
//! assignments, and the search then reports `unsat` for a satisfiable problem.
//! No gate in this repository can catch that: every gate validates a MODEL, and
//! a model exists only on the `sat` side. A wrong `unsat` is invisible to all of
//! them.
//!
//! So the DEFINING PROPERTY is checked independently of how the clause was
//! produced, and the checker was written first:
//!
//!   * **(a) FALSE under the current assignment** — [`clause_is_falsified`].
//!     Every clause literal is the negation of a literal asserted TRUE on the
//!     trail, so every disjunct is false.
//!   * **(b) A theory CONSEQUENCE** — [`clause_is_valid`]. The negation of the
//!     clause is the conjunction of the cited trail literals; the clause is
//!     implied exactly when that conjunction is unsatisfiable over the reals.
//!
//! [`explain_univariate`] returns `None` unless [`clause_is_valid`] PROVES
//! `true`. Returning `None` costs completeness; returning an unimplied clause
//! costs correctness. The trade is not close.
//!
//! # How (b) is decided, and why it is not the producer run twice
//!
//! The producer works in the **interval algebra**: it turns each literal into an
//! [`ialg::IntervalSet`] via [`ialg::from_sign_condition`] and intersects them.
//!
//! The checker does not touch that algebra at all. It decides validity by
//! **sign-invariant cell decomposition**: the real roots of every cited
//! polynomial, merged into one ascending list, cut `R` into `2n + 1` cells — `n`
//! root points and `n + 1` open gaps — on each of which every cited polynomial
//! has a constant sign. Testing one point per cell is therefore exhaustive, and
//! the clause is valid exactly when no cell satisfies every cited literal at
//! once. A cell that does satisfy them all is a COUNTEREXAMPLE, and it is a
//! concrete real number, not an absence of proof.
//!
//! Shared substrate, stated exactly (see the campaign's `same_set_as` finding —
//! a checker that shares its producer's code certifies its producer's bugs):
//! both sides call [`Anum::sign_of_poly`] (exact sign at a real algebraic
//! point), [`Anum::cmp_anum`] (exact comparison) and `anum`'s Sturm machinery.
//! Neither `IntervalSet`, `AInterval`, `Just`, `intersect`, `complement`,
//! `normalize`, `pick` nor `same_set_as` is reachable from the checker — the
//! whole interval algebra, which is where all three measured `ialg` defects
//! were, is off the checker's path. The oracle adds a leg beyond even that:
//! `explain-clause-implied` rebuilds the entire cell decomposition out of z3's
//! root isolation, z3's algebraic arithmetic and z3's sign evaluation, sharing
//! no AY code whatsoever.
//!
//! # Scope
//!
//! **Shipped:** the UNIVARIATE conflict — the polynomials are univariate in the
//! conflicting variable over `Z` (in an MCSAT search, this is the state after
//! the lower variables have been substituted out, and it is the `k = 1` case
//! exactly). Production, independent verification, and checker-gated
//! minimization.
//!
//! **Implemented and measured but NOT emitting clauses:** the CAD projection
//! operator ([`project`]) — leading coefficients, discriminants and pairwise
//! resultants, restricted by [`relevant_pairs`] to the pairs whose root ordering
//! actually matters at the sample point. It is a pure function with a degree
//! report, driven directly by the oracle.
//!
//! **Deferred, deliberately:** emitting a clause for the genuinely multivariate
//! conflict. That clause's validity rests on the CAD projection theorem
//! (delineability of the projection factors over the cell), which this module
//! cannot verify per instance — and by the rule at the top of this file, a
//! clause whose implication cannot be PROVED is not returned. Wiring that up
//! needs a per-instance delineability certificate, which is a separate piece of
//! work and is not pretended to exist here.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

use crate::anum::{self, Anum};
use crate::ialg::{self, IntervalSet, Just, SignCond};
use crate::mpbq::Bq;
use crate::subresultant::{self, MPolyZ, MVar, RPoly};
use crate::upoly::ZPoly;

// ============================================================================
// Ceilings — every one of them a DECLINE, never a truncation
// ============================================================================

/// Largest number of trail literals one conflict may cite.
///
/// The checker is `O(lits * cells)` sign evaluations and minimization multiplies
/// that by `lits`, so this bounds the whole module's work. A conflict citing
/// more than 64 sign conditions on one variable is past anything the cost
/// ceiling underneath admits: exact sign at an algebraic point is 6.7 ms at
/// degree 32, so 64 literals over a 64-cell decomposition is already 27 s.
pub(crate) const MAX_CONFLICT_LITS: usize = 64;

/// Largest number of distinct real roots the merged decomposition may have.
///
/// The merge is an insertion sort with a FALLIBLE comparator (`cmp_anum` returns
/// `Option`), so it cannot use `slice::sort_by`, which demands a total order;
/// converting an undecided comparison into a default is exactly the fail-open
/// this module refuses. `O(n^2)` comparisons at this ceiling is at most
/// `128 * 127 / 2 = 8,128` calls to [`Anum::cmp_anum`]. 128 roots means the
/// cited degrees sum to at least 128, far past the usable envelope (the MV
/// corpus median total degree is 3, max 44).
pub(crate) const MAX_CONFLICT_ROOTS: usize = 128;

/// Precision ladder for separating two adjacent algebraic roots by dyadics.
///
/// Doubling rather than incrementing: ten rungs reach `2^-256`. Two distinct
/// reals separated by less than that cost more to tell apart than the whole
/// search is worth, and `anum`'s own separation machinery declines there anyway.
/// **Exhausting the ladder returns `None`** — a decline, never a spin and never
/// a guessed midpoint.
const REFINE_KS: [u32; 10] = [0, 1, 2, 4, 8, 16, 32, 64, 128, 256];

/// Work budget above which minimization is skipped.
///
/// `cells * lits` sign evaluations per trial, `lits` trials. Skipping costs a
/// longer clause and nothing else — the clause returned is the one already
/// PROVED valid, so this ceiling cannot affect soundness, only size.
const MINIMIZE_BUDGET: usize = 4_096;

// ============================================================================
// Inputs
// ============================================================================

/// One literal on the trail: `p cond 0`, asserted TRUE.
///
/// `roots` is the ascending list of `p`'s real roots. It is taken as an
/// ARGUMENT rather than isolated here, for the same reason
/// [`ialg::from_sign_condition`] takes one: it makes every entry point in this
/// module a pure function the oracle can drive on z3's own root list, instead of
/// only through a consumer. It is **verified, not trusted** — see
/// [`roots_exact`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConflictLit {
    /// The trail literal's signed id. Never `0`.
    pub(crate) lit: i32,
    /// Integer coefficients, low-to-high.
    pub(crate) p: Vec<BigInt>,
    /// The sign condition asserted TRUE.
    pub(crate) cond: SignCond,
    /// Every real root of `p`, ascending. Verified.
    pub(crate) roots: Vec<Anum>,
}

/// A learned clause: `\/_j !L_j` over the cited trail literals.
///
/// # No stored verdict
///
/// This type carries the clause and nothing else. It deliberately has no
/// `is_valid` / `checked` / `verified` field, because the campaign's third
/// blind-spot pattern is "a stored flag the headline metric is read off", which
/// can be hardwired to the passing value with no divergence. Validity is
/// RE-DERIVED by calling [`clause_is_valid`] on the cited literals — the same
/// discipline `AlgCell::root_index` uses for the root index. The defect is made
/// unrepresentable rather than merely tested for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Explanation {
    lits: Vec<i32>,
    cited: Vec<i32>,
}

impl Explanation {
    /// The clause literals: the negation of each cited trail literal.
    pub(crate) fn lits(&self) -> &[i32] {
        &self.lits
    }

    /// The trail literals cited, ascending by absolute position of citation.
    pub(crate) fn cited(&self) -> &[i32] {
        &self.cited
    }

    /// How many literals the clause has.
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }
}

// ============================================================================
// PRIORITY 1(a): FALSE under the current assignment
// ============================================================================

/// Is every clause literal the negation of a literal asserted TRUE on `trail`?
///
/// That is exactly what makes the clause false under the current assignment: a
/// disjunct `!L` is false when `L` is true, and the clause is false when all of
/// them are.
///
/// Total, and deliberately so — there is nothing here that can decline, so
/// nothing that can hide a failure behind a refusal. The campaign found three
/// wrong answers made invisible by a check consuming a value with
/// `else { Declined }`; this predicate cannot participate in that.
pub(crate) fn clause_is_falsified(clause: &[i32], trail: &[i32]) -> bool {
    if clause.is_empty() {
        // The empty clause IS false under every assignment. Saying so is
        // correct; it is `clause_is_valid` that refuses to certify it.
        return true;
    }
    clause.iter().all(|&c| c != 0 && trail.contains(&-c))
}

// ============================================================================
// PRIORITY 1(b): a theory CONSEQUENCE
// ============================================================================

/// Is `roots` EXACTLY the real root list of `p` — no more and no fewer?
///
/// # Why all three tests, and not just the first
///
/// A previous lane checked that a root list ASCENDS and trusted that it was
/// COMPLETE. Dropping a root makes a non-empty feasible set look empty, which is
/// a conflict that does not exist, which in an MCSAT search is a wrong `unsat`.
/// For a CHECKER the same weakness is worse still: a checker that accepts a
/// short root list decomposes `R` into too few cells, misses the cell where the
/// conjunction is satisfiable, and CERTIFIES the very clause it exists to
/// refute. So the precondition is verified in both directions:
///
///   * **ascending and distinct** — the weak half, and the cheap one;
///   * **the COUNT is right** — a Sturm count over an interval strictly
///     containing every root, which settles completeness in one pass;
///   * **each listed value really is a root** — `sign_of_poly(p) == 0`. Count
///     alone does not give this: one real root missing and one spurious value
///     listed leaves the count correct.
///
/// This is strictly stronger than the producer's own precondition check
/// (`from_sign_condition` verifies ascending order and the count, not
/// membership), which is deliberate: the checker must not inherit the producer's
/// blind spots.
fn roots_exact(p: &[BigInt], roots: &[Anum]) -> Option<bool> {
    if roots.len() > MAX_CONFLICT_ROOTS {
        return None;
    }
    // The zero polynomial has sign 0 everywhere and no isolated roots; no finite
    // list describes its zero set, so the only correct list is the empty one.
    if p.iter().all(Zero::is_zero) {
        return Some(roots.is_empty());
    }
    let zp = ZPoly::from_coeffs(p.to_vec());
    // A non-zero constant has no roots at all.
    if zp.degree().unwrap_or(0) < 1 {
        return Some(roots.is_empty());
    }

    // Weak half: ascending and distinct.
    for w in roots.windows(2) {
        if w[0].cmp_anum(&w[1])? != Ordering::Less {
            return Some(false);
        }
    }

    // Strong half A: every listed value is genuinely a root of `p`.
    for r in roots {
        if r.sign_of_poly(p)? != 0 {
            return Some(false);
        }
    }

    // Strong half B: the COUNT is right, so none is missing.
    let sf = anum::normalize_defining(&zp)?;
    let chain = anum::sturm_chain(&sf)?;
    let b = anum::cauchy_bound_z(&sf)?;
    let lo = Bq::from_int(-(b.clone() + BigInt::one()));
    let hi = Bq::from_int(b + BigInt::one());
    // `sturm_count_in` counts DISTINCT real roots in `(lo, hi]`, and the bound
    // strictly encloses every root, so this is the total.
    let n = anum::sturm_count_in(&chain, &lo, &hi)?;
    Some(n == roots.len())
}

/// The upper dyadic handle of an algebraic number: a rational `>= a`, and
/// strictly `> a` whenever `a` is irrational.
fn upper_handle(a: &Anum) -> BigRational {
    match a {
        Anum::Rational(q) => q.clone(),
        // The isolating interval is OPEN and neither endpoint is a root, so the
        // root lies strictly inside: `a < hi`.
        Anum::Alg(c) => c.interval().hi().to_rational(),
    }
}

/// The lower dyadic handle: a rational `<= b`, strictly `< b` when `b` is
/// irrational.
fn lower_handle(b: &Anum) -> BigRational {
    match b {
        Anum::Rational(q) => q.clone(),
        Anum::Alg(c) => c.interval().lo().to_rational(),
    }
}

fn two() -> BigRational {
    BigRational::from_integer(BigInt::from(2))
}

/// A rational strictly between `a` and `b`, which must satisfy `a < b`.
///
/// Refines both isolating intervals down the [`REFINE_KS`] ladder until the
/// upper handle of `a` falls strictly below the lower handle of `b`; the
/// midpoint of those two rationals is then strictly between the two reals,
/// because `a <= upper(a) < mid < lower(b) <= b`.
///
/// # Liveness
///
/// **Exactly ten refinements, then one final test.** There is no
/// condition-driven loop: the ladder is a fixed array. Since `a < b` are
/// distinct reals and refinement drives each handle's error to `2^-k`, the test
/// succeeds for any `2^-k < (b - a) / 2`; a pair closer together than `2^-256`
/// exhausts the ladder and **returns `None`**. That is a decline, and every
/// caller propagates it. It is never a guessed midpoint — a midpoint that is not
/// actually between the two roots would put a sample point in the wrong cell,
/// which is precisely how a checker certifies a clause that is not valid.
fn strictly_between(a: &Anum, b: &Anum) -> Option<BigRational> {
    let mut ca = a.clone();
    let mut cb = b.clone();
    for &k in &REFINE_KS {
        let ua = upper_handle(&ca);
        let lb = lower_handle(&cb);
        if ua < lb {
            return Some((ua + lb) / two());
        }
        let target = Bq::new(BigInt::one(), k);
        ca = ca.refine(&target)?;
        cb = cb.refine(&target)?;
    }
    let ua = upper_handle(&ca);
    let lb = lower_handle(&cb);
    if ua < lb {
        return Some((ua + lb) / two());
    }
    None
}

/// Merge every cited literal's root list into one ascending, DISTINCT list.
///
/// # Liveness
///
/// Insertion sort, `O(n^2)` comparisons, refused above [`MAX_CONFLICT_ROOTS`]
/// before any comparison is made. The comparator is fallible and every `None`
/// propagates, so an undecided comparison declines the whole merge rather than
/// being defaulted into an order.
fn merge_roots(lits: &[ConflictLit]) -> Option<Vec<Anum>> {
    let total: usize = lits.iter().map(|l| l.roots.len()).sum();
    if total > MAX_CONFLICT_ROOTS {
        return None;
    }
    let mut out: Vec<Anum> = Vec::with_capacity(total);
    for l in lits {
        for r in &l.roots {
            let mut pos = out.len();
            let mut dup = false;
            for (i, existing) in out.iter().enumerate() {
                match r.cmp_anum(existing)? {
                    Ordering::Less => {
                        pos = i;
                        break;
                    }
                    Ordering::Equal => {
                        dup = true;
                        break;
                    }
                    Ordering::Greater => {}
                }
            }
            if !dup {
                out.insert(pos, r.clone());
            }
        }
    }
    Some(out)
}

/// One sample point per cell of the sign-invariant decomposition induced by
/// `roots`: `n` root points and `n + 1` open gaps, `2n + 1` in all.
///
/// Every cited polynomial has a constant sign on each open gap — the gaps
/// contain no root of any of them, by construction — so one point per gap plus
/// the roots themselves is an EXHAUSTIVE test of the real line.
///
/// # Liveness
///
/// One pass over `n` roots; `n` is already bounded by [`MAX_CONFLICT_ROOTS`] and
/// re-checked here rather than assumed.
fn sample_points(roots: &[Anum]) -> Option<Vec<Anum>> {
    if roots.len() > MAX_CONFLICT_ROOTS {
        return None;
    }
    if roots.is_empty() {
        // No roots anywhere: every cited polynomial has one constant sign on all
        // of `R`, so a single arbitrary point decides everything.
        return Some(vec![Anum::rational(BigRational::zero())]);
    }
    let mut out = Vec::with_capacity(2 * roots.len() + 1);

    // Strictly below every root. `lower_handle` of the smallest root is `< it`
    // when irrational; when rational, step down by one.
    let first = &roots[0];
    out.push(Anum::rational(match first {
        Anum::Rational(q) => q.clone() - BigRational::one(),
        Anum::Alg(_) => lower_handle(first),
    }));

    for (i, r) in roots.iter().enumerate() {
        out.push(r.clone());
        if let Some(next) = roots.get(i + 1) {
            out.push(Anum::rational(strictly_between(r, next)?));
        }
    }

    // Strictly above every root.
    let last = &roots[roots.len() - 1];
    out.push(Anum::rational(match last {
        Anum::Rational(q) => q.clone() + BigRational::one(),
        Anum::Alg(_) => upper_handle(last),
    }));

    Some(out)
}

/// **The defining property.** Is the clause `\/_j !L_j` VALID over the reals?
///
/// Equivalently: is `/\_j L_j` unsatisfiable? That is what makes the clause a
/// theory consequence, and it is the single highest-stakes question in this
/// module.
///
/// `Some(true)` is a PROOF: every cell of the sign-invariant decomposition was
/// enumerated and each one refuted at least one cited literal.
/// `Some(false)` is a COUNTEREXAMPLE: a cell satisfied all of them at once, so
/// the clause is not implied and must not be returned.
/// `None` is a DECLINE — a comparison, refinement or sign evaluation that could
/// not be decided.
///
/// # NEVER FAIL OPEN
///
/// The permissive answer here is `true` ("yes, it's implied"), and every path
/// that cannot decide something returns `None` instead of reaching it. A root
/// list that fails [`roots_exact`] declines rather than proceeding on a
/// decomposition that might be missing a cell; an undecidable sign declines
/// rather than assuming the literal fails. The campaign's worst defect was a
/// consistency predicate that answered "consistent" whenever it could not
/// evaluate its input, and this is the same shape of predicate in the same
/// position.
///
/// # Liveness
///
/// No condition-driven loop anywhere. `lits` is bounded by
/// [`MAX_CONFLICT_LITS`], the sample count by `2 * MAX_CONFLICT_ROOTS + 1`, and
/// the body is a nested pass over the two.
pub(crate) fn clause_is_valid(lits: &[ConflictLit]) -> Option<bool> {
    if lits.is_empty() {
        // The empty disjunction is `false`, which is not valid. Refusing to
        // certify it is the conservative answer and the correct one.
        return Some(false);
    }
    if lits.len() > MAX_CONFLICT_LITS {
        return None;
    }
    for l in lits {
        if l.lit == 0 {
            return None;
        }
        // Verified BEFORE anything consumes it, so a bad list cannot be
        // laundered into a verdict further down.
        if !roots_exact(&l.p, &l.roots)? {
            return None;
        }
    }

    let merged = merge_roots(lits)?;
    let samples = sample_points(&merged)?;

    for s in &samples {
        let mut all_hold = true;
        for l in lits {
            let sg = s.sign_of_poly(&l.p)?;
            if !l.cond.accepts(sg) {
                all_hold = false;
                break;
            }
        }
        if all_hold {
            // A real number satisfying every cited literal. The clause is NOT
            // implied.
            return Some(false);
        }
    }
    Some(true)
}

/// The counterexample [`clause_is_valid`] found, when there is one.
///
/// Returned separately so the oracle can adjudicate the WITNESS rather than the
/// verdict: an unwitnessed witness — a `false` nobody can check — is the
/// campaign's fourth blind-spot pattern. z3 evaluates the returned point against
/// every cited literal and must agree that all of them hold there.
pub(crate) fn clause_countermodel(lits: &[ConflictLit]) -> Option<Option<Anum>> {
    if lits.is_empty() || lits.len() > MAX_CONFLICT_LITS {
        return None;
    }
    for l in lits {
        if l.lit == 0 || !roots_exact(&l.p, &l.roots)? {
            return None;
        }
    }
    let merged = merge_roots(lits)?;
    let samples = sample_points(&merged)?;
    for s in &samples {
        let mut all_hold = true;
        for l in lits {
            if !l.cond.accepts(s.sign_of_poly(&l.p)?) {
                all_hold = false;
                break;
            }
        }
        if all_hold {
            return Some(Some(s.clone()));
        }
    }
    Some(None)
}

// ============================================================================
// PRIORITY 3: minimization, gated on the checker
// ============================================================================

/// Drop literals whose removal keeps the clause implied.
///
/// # Why this cannot break soundness
///
/// A literal is dropped ONLY when [`clause_is_valid`] PROVES the smaller clause
/// still valid. A decline (`None`) keeps the literal — the fail-closed direction,
/// since keeping a literal can only weaken the clause, never unsound it. The
/// checker is the authority for every intermediate state, so no chain of drops
/// can arrive somewhere unverified.
///
/// # Liveness
///
/// The outer loop runs EXACTLY `candidates.len()` times — it iterates a snapshot
/// taken before the first drop, not the shrinking set — and `candidates.len()`
/// is at most [`MAX_CONFLICT_LITS`]. Each iteration makes one bounded
/// [`clause_is_valid`] call. There is no re-entry and no fixpoint loop.
fn minimize(lits: &[ConflictLit], keep: &mut Vec<usize>) {
    let candidates: Vec<usize> = keep.clone();
    for c in candidates {
        if keep.len() <= 1 {
            break;
        }
        let trial: Vec<usize> = keep.iter().copied().filter(|&i| i != c).collect();
        let sub: Vec<ConflictLit> = trial.iter().map(|&i| lits[i].clone()).collect();
        // Only a PROVED-valid trial removes a literal. `None` and `Some(false)`
        // both keep it.
        if clause_is_valid(&sub) == Some(true) {
            *keep = trial;
        }
    }
}

// ============================================================================
// The producer
// ============================================================================

/// Explain a UNIVARIATE conflict: an empty feasible set becomes a learned clause.
///
/// Returns `None` when there is no conflict, when any step declines, or —
/// crucially — when the resulting clause cannot be PROVED implied.
///
/// # The justification gap this works around, measured
///
/// [`ialg::IntervalSet::justification`] cannot supply the conflict clause,
/// despite its doc comment saying it is what a caller needs when the set is
/// empty. It folds `merge` over `self.ivs`, and an empty set HAS no intervals,
/// so it returns `Just::none()` — the EMPTY justification — in exactly the case
/// it is documented for. `intersect` is where the information is lost: both its
/// early return (`if self.is_empty() || other.is_empty()`) and its ordinary exit
/// with no overlapping cells produce a bare `IntervalSet::empty()` carrying
/// nothing. `test_empty_intersection_loses_its_justification` pins this.
///
/// So this function tracks the cited literals ITSELF, in `cited`, rather than
/// reading them back out of the emptied set.
///
/// # Liveness
///
/// One pass over `lits` (bounded by [`MAX_CONFLICT_LITS`]), then one bounded
/// [`minimize`], then one bounded [`clause_is_valid`]. No condition-driven loop.
pub(crate) fn explain_univariate(lits: &[ConflictLit]) -> Option<Explanation> {
    if lits.is_empty() || lits.len() > MAX_CONFLICT_LITS {
        return None;
    }
    for l in lits {
        if l.lit == 0 {
            return None;
        }
    }

    // Fold the feasible sets, stopping at the first empty intersection. The
    // literals folded so far are the ones that emptied it.
    let mut acc = IntervalSet::full(Just::none());
    let mut cited: Vec<usize> = Vec::new();
    let mut conflict = false;
    for (i, l) in lits.iter().enumerate() {
        let fs = ialg::from_sign_condition(&l.p, &l.roots, l.cond, Just::of(l.lit)?)?;
        acc = acc.intersect(&fs)?;
        cited.push(i);
        if acc.is_empty() {
            conflict = true;
            break;
        }
    }
    if !conflict {
        // A non-empty feasible set is not a conflict, and inventing a clause for
        // it would prune a satisfiable region.
        return None;
    }

    let mut keep = cited;
    let cells = 2 * lits.iter().map(|l| l.roots.len()).sum::<usize>() + 1;
    if keep
        .len()
        .checked_mul(cells)
        .is_some_and(|w| w <= MINIMIZE_BUDGET)
    {
        minimize(lits, &mut keep);
    }

    let sub: Vec<ConflictLit> = keep.iter().map(|&i| lits[i].clone()).collect();

    // THE GATE. Not "the producer said so" — the clause is re-derived as a
    // theory consequence by an independent decision procedure, and anything
    // short of a proof is refused.
    if clause_is_valid(&sub)? != true {
        return None;
    }

    let cited_lits: Vec<i32> = sub.iter().map(|l| l.lit).collect();
    Some(Explanation {
        lits: cited_lits.iter().map(|&l| -l).collect(),
        cited: cited_lits,
    })
}

// ============================================================================
// PRIORITY 2: the projection
// ============================================================================

/// Which projection factor a polynomial came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProjKind {
    /// Leading coefficient of `polys[i]` in the projected variable — it
    /// vanishing is what makes the degree drop and the root structure change.
    LeadingCoeff(usize),
    /// Discriminant of `polys[i]` — its roots are where `polys[i]`'s own roots
    /// collide or leave the reals.
    Discriminant(usize),
    /// Resultant of `polys[i]` and `polys[j]` — its roots are where a root of
    /// one crosses a root of the other, which is where the ORDER of the cells
    /// changes.
    Resultant(usize, usize),
}

/// One projection factor and where it came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProjFactor {
    pub(crate) kind: ProjKind,
    pub(crate) poly: MPolyZ,
}

/// The projection, with the degree report the cost ceiling makes mandatory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Projection {
    pub(crate) factors: Vec<ProjFactor>,
    /// Largest total degree among the inputs.
    pub(crate) in_max_total_degree: u32,
    /// Largest total degree among the outputs.
    pub(crate) out_max_total_degree: u32,
    /// Outputs that are non-zero constants: no roots, so no cell boundary, so
    /// they contribute nothing to the decomposition of the lower space.
    pub(crate) constant_factors: usize,
}

/// Total degree of a multivariate integer polynomial.
fn mpoly_total_degree(p: &MPolyZ) -> u32 {
    p.terms()
        .iter()
        .map(|(m, _)| m.pairs().iter().map(|&(_, e)| e).sum::<u32>())
        .max()
        .unwrap_or(0)
}

/// Total degree of a polynomial in `x` whose coefficients live in `Z[lower]`.
fn bipoly_total_degree(p: &RPoly<MPolyZ>) -> u32 {
    p.coeffs()
        .iter()
        .enumerate()
        .filter(|(_, c)| !subresultant::ExactRing::is_zero(*c))
        .map(|(i, c)| {
            u32::try_from(i)
                .unwrap_or(u32::MAX)
                .saturating_add(mpoly_total_degree(c))
        })
        .max()
        .unwrap_or(0)
}

/// The pairs whose root ORDERING actually matters at the sample point.
///
/// The full CAD projection takes a resultant for every pair, which is
/// `O(m^2)` resultants and — since a resultant multiplies degrees — the
/// dominant cost. Only pairs that are ADJACENT in the merged root order can
/// change the cell decomposition by crossing, so only those need a resultant:
/// two polynomials whose roots are separated by a third polynomial's root
/// cannot swap without that third root being crossed first, and THAT crossing
/// is already covered by its own pair.
///
/// Returns pairs `(i, j)` with `i < j`, deduplicated, indexing into `lits`.
///
/// # Liveness
///
/// One merge (bounded by [`MAX_CONFLICT_ROOTS`]) and one pass over the merged
/// list. The dedup is an `O(p^2)` scan over at most `MAX_CONFLICT_ROOTS` pairs.
pub(crate) fn relevant_pairs(lits: &[ConflictLit]) -> Option<Vec<(usize, usize)>> {
    if lits.len() > MAX_CONFLICT_LITS {
        return None;
    }
    let total: usize = lits.iter().map(|l| l.roots.len()).sum();
    if total > MAX_CONFLICT_ROOTS {
        return None;
    }
    // (root, owning literal index), ascending by root. Equal roots from
    // different owners are BOTH kept: a shared root is the strongest possible
    // reason for a pair to matter.
    let mut tagged: Vec<(Anum, usize)> = Vec::with_capacity(total);
    for (i, l) in lits.iter().enumerate() {
        for r in &l.roots {
            let mut pos = tagged.len();
            for (k, (existing, _)) in tagged.iter().enumerate() {
                if r.cmp_anum(existing)? == Ordering::Less {
                    pos = k;
                    break;
                }
            }
            tagged.insert(pos, (r.clone(), i));
        }
    }
    let mut out: Vec<(usize, usize)> = Vec::new();
    for w in tagged.windows(2) {
        let (a, b) = (w[0].1, w[1].1);
        if a == b {
            continue;
        }
        let pair = (a.min(b), a.max(b));
        if !out.contains(&pair) {
            out.push(pair);
        }
    }
    Some(out)
}

/// The CAD projection operator, restricted to `pairs`.
///
/// Leading coefficients and discriminants of every input, plus the resultant of
/// each listed pair. This is the projection that a multivariate explanation
/// would cite; it is a PURE function here, driven directly by the oracle, and
/// its output is **not** turned into a clause — see the module header for why.
///
/// # Liveness
///
/// `polys.len()` leading coefficients, `polys.len()` discriminants and
/// `pairs.len()` resultants, all bounded by [`MAX_CONFLICT_LITS`] and its
/// square. Every underlying subresultant call is itself bounded and fallible,
/// and every `None` propagates.
pub(crate) fn project(polys: &[RPoly<MPolyZ>], pairs: &[(usize, usize)]) -> Option<Projection> {
    if polys.is_empty() || polys.len() > MAX_CONFLICT_LITS {
        return None;
    }
    let in_max_total_degree = polys.iter().map(bipoly_total_degree).max().unwrap_or(0);
    let mut factors: Vec<ProjFactor> = Vec::new();

    for (i, p) in polys.iter().enumerate() {
        // Degree in the projected variable below 1 means the polynomial does not
        // constrain that variable at all; it has no leading coefficient in it
        // and no discriminant. Skipping is not a fail-open: such a polynomial
        // induces no cell boundary in the projected variable, so it contributes
        // nothing to project.
        if p.degree().unwrap_or(0) < 1 {
            continue;
        }
        let lc = p.leading()?.clone();
        factors.push(ProjFactor {
            kind: ProjKind::LeadingCoeff(i),
            poly: lc,
        });
        let disc = subresultant::discriminant(p)?;
        factors.push(ProjFactor {
            kind: ProjKind::Discriminant(i),
            poly: disc,
        });
    }

    for &(i, j) in pairs {
        if i >= polys.len() || j >= polys.len() || i == j {
            return None;
        }
        let res = subresultant::resultant(&polys[i], &polys[j])?;
        factors.push(ProjFactor {
            kind: ProjKind::Resultant(i, j),
            poly: res,
        });
    }

    let out_max_total_degree = factors
        .iter()
        .map(|f| mpoly_total_degree(&f.poly))
        .max()
        .unwrap_or(0);
    let constant_factors = factors
        .iter()
        .filter(|f| !subresultant::ExactRing::is_zero(&f.poly) && mpoly_total_degree(&f.poly) == 0)
        .count();

    Some(Projection {
        factors,
        in_max_total_degree,
        out_max_total_degree,
        constant_factors,
    })
}

/// Degree of `p` in variable `v`, for the degree report.
pub(crate) fn degree_in(p: &MPolyZ, v: MVar) -> u32 {
    p.terms()
        .iter()
        .map(|(m, _)| {
            m.pairs()
                .iter()
                .find(|&&(w, _)| w == v)
                .map_or(0, |&(_, e)| e)
        })
        .max()
        .unwrap_or(0)
}

/// Signed-ness helper kept so `Signed` is used; the sign of a polynomial's
/// leading coefficient is what orients a projection factor.
pub(crate) fn lc_sign(p: &[BigInt]) -> i32 {
    match p.iter().rev().find(|c| !c.is_zero()) {
        Some(c) if c.is_negative() => -1,
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(test)]
#[path = "explain_tests.rs"]
mod explain_tests;
