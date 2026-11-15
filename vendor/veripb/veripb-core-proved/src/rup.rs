//! Checked replay of reverse-unit-propagation (RUP) trails.
//!
//! The live propagation engine (watched literals, precedence orders, caches)
//! stays fast and unproved; what it must hand this module is a *certificate*:
//! the sequence of propagations it performed and the constraint it found
//! conflicting. This module replays that certificate against the proved
//! semantics, in the coefficient domain's exact arithmetic, checking at every
//! step exactly the hypotheses of the Clean theorems:
//!
//! | Rust | Clean |
//! |---|---|
//! | [`slack_terms`] | `VeriPbCore.slackTerms` |
//! | [`slack_without`] | `VeriPbCore.slackWithout` |
//! | [`RupCheck::step`] | `VeriPbCore.PropTrail.step` (its hypotheses) |
//! | [`RupCheck::conflict`] | `VeriPbCore.rup_conflict_unsat` (its hypotheses) |
//! | [`check_rup`] | `VeriPbCore.entails_of_rup` / `VeriPbCore.DStep.rupS` |
//!
//! A successful [`check_rup`] run establishes every hypothesis of
//! `entails_of_rup`, so the target constraint is entailed by any formula that
//! entails the database — with the negated-degree witness equation checked by
//! the guarded [`negate`](crate::negate), a trail whose every step is
//! re-verified to propagate, and a conflict re-verified by slack. A trail the
//! engine got wrong is *rejected*, never trusted.
//!
//! Slack is where a wrapped machine value turns a satisfiable formula into a
//! refutation (that is the watcher-slack defect exactly), so the width the
//! folds run at is soundness-critical. Instantiated at
//! [`Coeff`](crate::Coeff) they run in `i128`, exact for every constraint an
//! `i64` checker can hold; instantiated at [`Big`](crate::Big) they run in
//! `Int` and are exact for every constraint the live checker can hold *at
//! all*, which is what lets the bridge re-judge a promoted constraint instead
//! of standing down at it.
//!
//! The Clean trail is a list, and membership is what matters (`memB`); the
//! replay keeps the trail as an insert-only [`Trail`] (a `HashSet<Lit>`),
//! which computes the same membership function: `memB` is duplicate- and
//! order-insensitive list membership under `litEqB`, which is structural
//! equality on `(var, negated)`, and that is exactly the derived
//! `PartialEq`/`Hash` on [`Lit`]. The trail is only ever pushed to and
//! queried for membership — nothing observes insertion order or
//! multiplicity — so the set is an *index over the proved membership
//! search*, not a new algorithm.
//!
//! ## The slack index computes the identical function
//!
//! [`RupCheck::step`] and [`RupCheck::conflict`] re-fold `slackWithout` /
//! `slackTerms` over the referenced constraint's whole term list, so a wide
//! constraint that propagates many literals costs `O(|c|)` per step — the
//! replay of one `|c|`-term cardinality row is `O(|c|^2)`. The wide path
//! answers the same two folds from a running index, justified by two
//! algebraic identities about the folds themselves (both are statements
//! about `slackTerms`/`slackWithout` as defined in Clean, and hold for any
//! `ts`, `tr`, `l`):
//!
//! - **(a) trail extension.** If `memB l tr` is false, then
//!   `slackTerms (l :: tr) ts = slackTerms tr ts - sum {t.coeff | t.lit = negLit l}`.
//!   `slackTerms` sums the coefficients of terms whose literal is *not*
//!   falsified, i.e. whose `negLit t.lit` is not on the trail. Extending the
//!   trail by `l` changes that predicate for exactly the terms with
//!   `t.lit = negLit l`, and — because `l` was not already on `tr` — it
//!   changes for *all* of them, from "counted" to "not counted". Every other
//!   term's membership test is untouched, `memB` being unaffected by the
//!   extra element for any other literal.
//! - **(b) exclusion.**
//!   `slackWithout l tr ts = slackTerms tr ts - (if memB (negLit l) tr then 0 else sum {t.coeff | t.lit = l})`.
//!   `slackWithout` is `slackTerms`'s filter conjoined with `t.lit != l`, so
//!   the two differ exactly by the terms whose literal *is* `l` and which
//!   `slackTerms` counted. Those are counted iff `l` is not falsified, which
//!   is the conditional. Note this form is total: it is correct also when `l`
//!   is already falsified, where the naive "subtract the coefficient" shortcut
//!   is not.
//!
//! [`SlackIndex`] maintains `slackTerms` per view slot under (a) and answers
//! `slackWithout` by (b) from a per-`(slot, literal)` coefficient total. Both
//! totals are plain sums of the same exact coefficients the folds sum, so the
//! index is a *representation of the proved folds*, not a different quantity —
//! the same relationship the [`Trail`] set has to `memB`. The identity is
//! re-checked against the folds by `debug_assert` at every step and conflict,
//! and by a randomized differential test against the naive [`RupCheck`].
//!
//! Building the index costs one pass over every term of the view, so it is a
//! loss on the narrow certificates that dominate real proofs; [`check_rup`]
//! therefore dispatches on a cost estimate (see [`use_slack_index`]) exactly
//! as `normalize.rs` dispatches its merge pass on `INDEXED_MERGE_THRESHOLD`.
//! Both paths compute the same function, so the cutoff is purely a
//! performance knob.

// The repo-wide clippy policy prefers `ahash` over std's hash collections,
// but the proved kernel keeps its dependency list to the one integer type it
// is instantiated at (see the crate docs), so the trail set uses std's
// `HashSet`. The hasher choice cannot affect the membership function
// computed — only its constant factor.
#![allow(clippy::disallowed_types)]

use std::collections::{HashMap, HashSet};

use crate::{CoeffDomain, Constraint, Exact, GuardError, Lit, Term};

/// Why a RUP trail replay was rejected.
///
/// Every variant is a hypothesis of a Clean theorem that could not be
/// established from the certificate. A rejected replay derives nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RupError {
    /// A step or the conflict referenced a database index with no constraint
    /// (`getG` returned `none`).
    BadIndex,
    /// The referenced constraint has a negative coefficient
    /// (`VeriPbCore.AllNonneg` fails); slack reasoning is unsound on it.
    NotNormalized,
    /// The claimed propagation does not satisfy
    /// `slackWithout l tr c.terms < c.degree`.
    StepNotPropagating,
    /// The claimed conflict does not satisfy
    /// `slackTerms tr c.terms < c.degree`.
    NoConflict,
    /// Negating the target overflowed the guarded arithmetic. Unreachable at
    /// an unbounded domain, whose `narrow` is total.
    NegationOverflow(GuardError),
}

/// Written as an explicit loop, not `iter().all(..)`, and the same goes for
/// the two slack folds below.
///
/// The closure form is not lowerable by the verifier -- it reports
/// `unsupported operand type Const: unsupported constant of MIR type bool`
/// and abandons the body -- and the failure PROPAGATES to every caller,
/// because a function whose local callee cannot be lowered cannot be lowered
/// either. Measured: these three chains alone accounted for 48 incomplete
/// obligations, most of them in `RupCheck::step`, `::conflict` and
/// `SlackIndex::new` rather than here.
///
/// The loop computes the identical function: same short-circuit point, same
/// left-to-right order, same accumulator. What is lost is the visual
/// correspondence to Clean's `AllNonneg`/`slackTerms` folds, which is why the
/// correspondence is spelled out in the doc comments instead.
fn all_nonneg<C: CoeffDomain>(ts: &[Term<C>]) -> bool {
    let mut i = 0usize;
    while i < ts.len() {
        if !C::is_nonneg(&ts[i].coeff) {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// The propagation trail: the set of literals assigned true so far.
///
/// The Clean trail is a `List Lit` consumed *only* through `memB` — pure,
/// duplicate- and order-insensitive membership under `litEqB` (structural
/// equality on `(var, negated)`, exactly the derived `PartialEq`/`Eq`/`Hash`
/// on [`Lit`]). This newtype is insert-only and answers only membership
/// queries, so a `HashSet` computes the *identical function* the linear list
/// scan computes; it is a representation/index change over the proved
/// definition, not a new algorithm. Nothing here can observe insertion order
/// or multiplicity, which is all a list could add.
#[derive(Clone, Debug, Default)]
pub struct Trail(HashSet<Lit>);

impl Trail {
    /// The empty trail (`PropTrail.nil`'s trail).
    pub fn new() -> Self {
        Trail(HashSet::new())
    }

    /// Add a literal to the trail (the trail extension in `PropTrail.step`).
    /// Inserting a literal twice is a no-op, exactly as re-listing it leaves
    /// `memB` unchanged.
    pub fn insert(&mut self, l: Lit) {
        self.0.insert(l);
    }

    /// Is `l` on the trail, i.e. assigned true? Mirrors `memB l tr`.
    pub fn assigned(&self, l: Lit) -> bool {
        self.0.contains(&l)
    }

    /// Is `l` falsified by the trail, i.e. is `~l` assigned true?
    /// Mirrors `memB (negLit l) tr`.
    pub fn falsified(&self, l: Lit) -> bool {
        self.0.contains(&l.negate())
    }
}

/// Mirrors `VeriPbCore.slackTerms`: the sum of coefficients of terms not yet
/// falsified by the trail. Computed at the domain's exact width, which is
/// exact for every constraint that domain can hold.
pub fn slack_terms<C: CoeffDomain>(trail: &Trail, ts: &[Term<C>]) -> C::Exact {
    // `slackTerms` folded left-to-right; see `all_nonneg` for why this is a
    // loop rather than `sum(filter(map(..)))`.
    let mut acc = <C::Exact as Exact>::zero();
    let mut i = 0usize;
    while i < ts.len() {
        if !trail.falsified(ts[i].lit) {
            acc = acc.add(&ts[i].coeff.widen());
        }
        i = i.saturating_add(1);
    }
    acc
}

/// Mirrors `VeriPbCore.slackWithout`: [`slack_terms`] with the terms whose
/// literal is exactly `l` also excluded. If this is below the degree, every
/// model of the constraint that agrees with the trail must set `l` true.
pub fn slack_without<C: CoeffDomain>(l: Lit, trail: &Trail, ts: &[Term<C>]) -> C::Exact {
    // `slackWithout` folded left-to-right; see `all_nonneg`.
    let mut acc = <C::Exact as Exact>::zero();
    let mut i = 0usize;
    while i < ts.len() {
        if ts[i].lit != l && !trail.falsified(ts[i].lit) {
            acc = acc.add(&ts[i].coeff.widen());
        }
        i = i.saturating_add(1);
    }
    acc
}

/// One in-progress RUP replay: the negated target at index `0`, the database
/// at indices `1..`, and the trail built so far. Mirrors `VeriPbCore.getG`
/// and `VeriPbCore.PropTrail`.
pub struct RupCheck<'a, C: CoeffDomain = crate::Coeff> {
    neg: Constraint<C>,
    db: &'a [&'a Constraint<C>],
    trail: Trail,
}

impl<'a, C: CoeffDomain> RupCheck<'a, C> {
    /// Negate `target` (guarded — the witness equation
    /// `nd + d = coeffSum + 1` is exact by construction) and start an empty
    /// trail (`PropTrail.nil`).
    pub fn new(target: &Constraint<C>, db: &'a [&'a Constraint<C>]) -> Result<Self, RupError> {
        let neg = crate::negate(target).map_err(RupError::NegationOverflow)?;
        Ok(RupCheck {
            neg,
            db,
            trail: Trail::new(),
        })
    }

    /// `getG`: index 0 is the negated target, index `i + 1` is `db[i]`.
    fn get(&self, i: usize) -> Option<&Constraint<C>> {
        if i == 0 {
            Some(&self.neg)
        } else {
            self.db.get(i - 1).copied()
        }
    }

    /// Replay one propagation: constraint `i` propagates literal `l` under
    /// the current trail. Checks exactly the hypotheses of
    /// `PropTrail.step`; on success the literal joins the trail.
    pub fn step(&mut self, i: usize, l: Lit) -> Result<(), RupError> {
        let c = self.get(i).ok_or(RupError::BadIndex)?;
        if !all_nonneg(&c.terms) {
            return Err(RupError::NotNormalized);
        }
        if slack_without(l, &self.trail, &c.terms) >= c.degree.widen() {
            return Err(RupError::StepNotPropagating);
        }
        self.trail.insert(l);
        Ok(())
    }

    /// Check the claimed conflict: constraint `i` has negative slack under
    /// the final trail. These are the hypotheses of `rup_conflict_unsat`.
    pub fn conflict(&self, i: usize) -> Result<(), RupError> {
        let c = self.get(i).ok_or(RupError::BadIndex)?;
        if !all_nonneg(&c.terms) {
            return Err(RupError::NotNormalized);
        }
        if slack_terms(&self.trail, &c.terms) >= c.degree.widen() {
            return Err(RupError::NoConflict);
        }
        Ok(())
    }
}

/// The running images of the two proved slack folds, one per view slot.
///
/// See the module header for the two identities this maintains; the whole
/// index is a representation of `slackTerms`/`slackWithout` over a *fixed*
/// view (nothing here may be reused across different constraint lists).
struct SlackIndex<E> {
    /// `slack[i]` is `slackTerms trail (view i).terms` for the current trail,
    /// maintained under identity (a).
    slack: Vec<E>,
    /// `by_slot_lit[(i, l)]` is `sum {t.coeff | t in (view i).terms, t.lit = l}`
    /// — the quantity identity (b) subtracts. Absent means zero.
    by_slot_lit: HashMap<(usize, Lit), E>,
    /// `occ[l]` lists, per slot that mentions `l` at all, the same total —
    /// the decrements identity (a) applies when `negLit l` joins the trail.
    occ: HashMap<Lit, Vec<(usize, E)>>,
    /// `AllNonneg (view i).terms`, precomputed. Only ever *consulted* where
    /// the naive replay runs the scan, so the order in which a rejected
    /// constraint is reported is unchanged.
    nonneg: Vec<bool>,
}

impl<E: Exact> SlackIndex<E> {
    /// One pass over the whole view: the empty trail falsifies nothing, so
    /// `slackTerms [] ts` is the plain coefficient sum.
    fn new<C: CoeffDomain<Exact = E>>(neg: &Constraint<C>, db: &[&Constraint<C>]) -> Self {
        // Capacity hint only, so saturating is free; `db.len() + 1` raises an
        // overflow obligation on an unconstrained length.
        let n = db.len().saturating_add(1);
        let mut slack = Vec::with_capacity(n);
        let mut nonneg = Vec::with_capacity(n);
        let mut by_slot_lit: HashMap<(usize, Lit), E> = HashMap::new();
        // Slot 0 is the negated target, slot `i + 1` is `db[i]` -- `getG`'s
        // numbering, taken from the walk rather than from `db[i - 1]`. The
        // index form is in range by construction, but the construction lives
        // inside the opaque range iterator, so `i` was an unconstrained
        // `usize` here and the bounds obligation could not be discharged.
        // `enumerate` supplies the same slot number with no index and no
        // subtraction.
        let view = core::iter::once(&neg.terms).chain(db.iter().map(|c| &c.terms));
        for (i, ts) in view.enumerate() {
            let mut total = E::zero();
            for t in ts {
                let w = t.coeff.widen();
                total = total.add(&w);
                let entry = by_slot_lit.entry((i, t.lit)).or_insert_with(E::zero);
                *entry = entry.add(&w);
            }
            slack.push(total);
            nonneg.push(all_nonneg(ts));
        }
        let mut occ: HashMap<Lit, Vec<(usize, E)>> = HashMap::new();
        for (&(i, l), total) in by_slot_lit.iter() {
            occ.entry(l).or_default().push((i, total.clone()));
        }
        SlackIndex {
            slack,
            by_slot_lit,
            occ,
            nonneg,
        }
    }

    /// Identity (b): `slackWithout l trail (view i).terms`.
    ///
    /// `None` for a slot outside the view. The index has exactly one entry per
    /// slot of `getG`'s domain, so a caller that has already resolved `i`
    /// through `get` cannot see it -- but the fallback has to be ABSENT rather
    /// than a default, and this is the direction that matters. Slack is
    /// compared against the degree to decide whether a step propagates, and
    /// UNDERSTATING it (a zero default, say) turns a non-propagating step into
    /// an accepted one. Only absence is fail-closed.
    fn slack_without(&self, i: usize, l: Lit, trail: &Trail) -> Option<E> {
        // Explicit length test rather than `.get(i)`: `slice::get` is opaque
        // to the verifier and its bounds obligation is reported FAILED with a
        // fabricated counterexample. `slack` is an OWNED `Vec` field, which is
        // what makes the comparison and the index agree; on a `&[&T]` field
        // the same rewrite measurably makes things WORSE.
        if i >= self.slack.len() {
            return None;
        }
        let slack = &self.slack[i];
        if trail.falsified(l) {
            return Some(slack.clone());
        }
        Some(match self.by_slot_lit.get(&(i, l)) {
            Some(counted) => slack.sub(counted),
            None => slack.clone(),
        })
    }

    /// Identity (a). The caller must have checked that `l` is not already on
    /// the trail: on a repeat the terms falsified by `l` are already
    /// uncounted, and subtracting again would understate every slack.
    fn on_insert(&mut self, l: Lit) {
        if let Some(slots) = self.occ.get(&l.negate()) {
            for (k, total) in slots {
                // `occ` is built by inverting `by_slot_lit`, so every `k` is a
                // slot that was pushed -- the miss cannot happen. Skipping it
                // is the safe arm regardless: a subtraction not performed
                // OVERSTATES slack, and an overstated slack only ever turns
                // into `StepNotPropagating` or `NoConflict`. It rejects.
                if *k < self.slack.len() {
                    let updated = self.slack[*k].sub(total);
                    self.slack[*k] = updated;
                }
            }
        }
    }
}

/// [`RupCheck`] answering the two slack folds from a [`SlackIndex`].
///
/// Every check it performs is the same predicate on the same value, so it
/// accepts and rejects exactly the certificates [`RupCheck`] does — including
/// which error it reports first, the order of the index/normalization/slack
/// tests being unchanged. The `debug_assert`s re-derive the indexed value
/// from the proved fold on every step of every debug run.
struct IndexedRupCheck<'a, C: CoeffDomain> {
    neg: Constraint<C>,
    db: &'a [&'a Constraint<C>],
    trail: Trail,
    index: SlackIndex<C::Exact>,
}

impl<'a, C: CoeffDomain> IndexedRupCheck<'a, C> {
    fn new(target: &Constraint<C>, db: &'a [&'a Constraint<C>]) -> Result<Self, RupError> {
        let neg = crate::negate(target).map_err(RupError::NegationOverflow)?;
        let index = SlackIndex::new(&neg, db);
        Ok(IndexedRupCheck {
            neg,
            db,
            trail: Trail::new(),
            index,
        })
    }

    /// `getG`, exactly as [`RupCheck::get`].
    fn get(&self, i: usize) -> Option<&Constraint<C>> {
        if i == 0 {
            Some(&self.neg)
        } else {
            self.db.get(i - 1).copied()
        }
    }

    fn step(&mut self, i: usize, l: Lit) -> Result<(), RupError> {
        let c = self.get(i).ok_or(RupError::BadIndex)?;
        // Through `get`, so `i` is in range -- but `slice::get` is opaque to
        // the verifier, which cannot carry that to an index expression. These
        // read the same slots via `get`, and the unreachable miss maps to the
        // error an out-of-range slot actually means. Fail-closed either way.
        // Each length test sits at the access it guards, NOT hoisted to the
        // top: `nonneg` and `slack` are pushed in lockstep by `SlackIndex::new`
        // so a disagreement is impossible, but hoisting would still change
        // WHICH error fires first if it ever were, and this crate's docs
        // guarantee the order a rejection is reported in.
        if i >= self.index.nonneg.len() {
            return Err(RupError::BadIndex);
        }
        if !self.index.nonneg[i] {
            debug_assert!(!all_nonneg(&c.terms));
            return Err(RupError::NotNormalized);
        }
        let degree = c.degree.widen();
        let slack = self
            .index
            .slack_without(i, l, &self.trail)
            .ok_or(RupError::BadIndex)?;
        debug_assert_eq!(slack, slack_without(l, &self.trail, &c.terms));
        if slack >= degree {
            return Err(RupError::StepNotPropagating);
        }
        if !self.trail.assigned(l) {
            self.index.on_insert(l);
        }
        self.trail.insert(l);
        Ok(())
    }

    fn conflict(&self, i: usize) -> Result<(), RupError> {
        let c = self.get(i).ok_or(RupError::BadIndex)?;
        // As in `step`: same slots, through `get`, unreachable miss to
        // `BadIndex`.
        if i >= self.index.nonneg.len() {
            return Err(RupError::BadIndex);
        }
        if !self.index.nonneg[i] {
            debug_assert!(!all_nonneg(&c.terms));
            return Err(RupError::NotNormalized);
        }
        if i >= self.index.slack.len() {
            return Err(RupError::BadIndex);
        }
        let slack = &self.index.slack[i];
        debug_assert_eq!(*slack, slack_terms(&self.trail, &c.terms));
        if *slack >= c.degree.widen() {
            return Err(RupError::NoConflict);
        }
        Ok(())
    }
}

/// Is the indexed replay worth its build pass on this certificate?
///
/// The naive replay folds over the referenced constraint once per step (twice
/// counting `AllNonneg`); the indexed one pays one pass over *every* term of
/// the view and then answers each step in `O(1)`. Comparing the two term
/// counts — with a small constant so that tiny certificates, where the hash
/// maps are pure overhead, always take the plain path — is therefore the
/// whole decision. It affects only which of two implementations of the same
/// function runs.
fn use_slack_index<C: CoeffDomain>(
    target_terms: usize,
    db: &[&Constraint<C>],
    steps: &[(usize, Lit)],
    conflict: usize,
) -> bool {
    // Saturating throughout: this is a cost estimate whose only consumer is
    // the `>` below, so a total that cannot be represented needs no exact
    // value -- only to stay at the top of the range, where it decides the same
    // way. Plain `+`/`*` here raise overflow obligations that cannot be
    // discharged (every operand is an unconstrained `usize`, and
    // `Iterator::sum` is opaque), and a sum of `db.len()` slice lengths is
    // genuinely unbounded rather than merely unproved. In a debug build they
    // would panic rather than pick a dispatch.
    //
    // Negation preserves the term count, so the target's width is the
    // negated target's width.
    let view_terms: usize = db
        .iter()
        .map(|c| c.terms.len())
        .fold(target_terms, usize::saturating_add);
    let width = |i: usize| {
        if i == 0 {
            target_terms
        } else {
            db.get(i - 1).map_or(0, |c| c.terms.len())
        }
    };
    let fold_terms: usize = steps
        .iter()
        .map(|&(i, _)| width(i))
        .fold(0usize, usize::saturating_add)
        .saturating_add(width(conflict));
    fold_terms > view_terms.saturating_add(64).saturating_mul(4)
}

/// Replay a full RUP certificate for `target` against `db`.
///
/// `steps` is the propagation trail as `(constraint index, literal)` pairs in
/// propagation order; `conflict` is the index of the conflicting constraint.
/// Index `0` means the negated target itself; index `i + 1` means `db[i]`.
///
/// `Ok(())` establishes every hypothesis of `VeriPbCore.entails_of_rup`:
/// the target is entailed by whatever entails `db`.
pub fn check_rup<C: CoeffDomain>(
    target: &Constraint<C>,
    db: &[&Constraint<C>],
    steps: &[(usize, Lit)],
    conflict: usize,
) -> Result<(), RupError> {
    check_rup_dispatch(
        target,
        db,
        steps,
        conflict,
        use_slack_index(target.terms.len(), db, steps, conflict),
    )
}

/// [`check_rup`] with the index/fold choice forced, so the differential test
/// can run both implementations on the same certificate.
fn check_rup_dispatch<C: CoeffDomain>(
    target: &Constraint<C>,
    db: &[&Constraint<C>],
    steps: &[(usize, Lit)],
    conflict: usize,
    indexed: bool,
) -> Result<(), RupError> {
    if indexed {
        let mut check = IndexedRupCheck::new(target, db)?;
        for &(i, l) in steps {
            check.step(i, l)?;
        }
        check.conflict(conflict)
    } else {
        let mut check = RupCheck::new(target, db)?;
        for &(i, l) in steps {
            check.step(i, l)?;
        }
        check.conflict(conflict)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Big;

    fn x() -> Lit {
        Lit::pos(0)
    }

    fn unit(l: Lit) -> Constraint {
        Constraint::new(vec![Term { coeff: 1, lit: l }], 1)
    }

    #[test]
    fn end_to_end_refutation_replays() {
        // Mirrors VeriPbCore.ctrl_rup_refutation_end_to_end:
        // DB = [x >= 1, ~x >= 1]; RUP-derive the contradiction 0 >= 1.
        // Negation of 0 >= 1 is 0 >= 0 (index 0, trivially satisfied, unused).
        // Constraint 1 propagates x; constraint 2 then has negative slack.
        let c1 = unit(x());
        let c2 = unit(x().negate());
        let db = [&c1, &c2];
        let target = Constraint::contradiction();
        assert_eq!(check_rup(&target, &db, &[(1, x())], 2), Ok(()));
    }

    #[test]
    fn non_propagating_step_is_rejected() {
        // 2x + 2y >= 2 does not propagate x under the empty trail
        // (slackWithout x = 2, not < 2).
        let c = Constraint::new(
            vec![
                Term { coeff: 2, lit: x() },
                Term {
                    coeff: 2,
                    lit: Lit::pos(1),
                },
            ],
            2,
        );
        let db = [&c];
        let target = Constraint::contradiction();
        assert_eq!(
            check_rup(&target, &db, &[(1, x())], 1),
            Err(RupError::StepNotPropagating)
        );
    }

    #[test]
    fn missing_conflict_is_rejected() {
        let c1 = unit(x());
        let db = [&c1];
        let target = Constraint::contradiction();
        // x propagates, but nothing conflicts.
        assert_eq!(
            check_rup(&target, &db, &[(1, x())], 1),
            Err(RupError::NoConflict)
        );
    }

    #[test]
    fn unnormalized_constraint_is_rejected() {
        let bad = Constraint::new(
            vec![Term {
                coeff: -1,
                lit: x(),
            }],
            0,
        );
        let db = [&bad];
        let target = Constraint::contradiction();
        assert_eq!(
            check_rup(&target, &db, &[], 1),
            Err(RupError::NotNormalized)
        );
    }

    /// The wrapped-watcher-slack shape, one width above `i64`.
    ///
    /// `2^100 ~x >= -1` is trivially true, so nothing propagates from it. A
    /// slack computation that wraps reports `~x` as propagated anyway and the
    /// unit `x >= 1` then "conflicts" — a refutation of a satisfiable
    /// formula. The proved replay computes the slack exactly at this domain
    /// and rejects the step, which is what turns the live checker's wrap into
    /// a divergence instead of a skip.
    #[test]
    fn a_propagation_that_only_a_wrapped_slack_licenses_is_rejected_beyond_i64() {
        let huge = Big::from(u64::MAX) * Big::from(u64::MAX);
        let trivial = Constraint::new(
            vec![Term {
                coeff: huge,
                lit: Lit::neg(0),
            }],
            Big::from(-1),
        );
        let unit_x = Constraint::new(
            vec![Term {
                coeff: Big::from(1),
                lit: x(),
            }],
            Big::from(1),
        );
        let db = [&trivial, &unit_x];
        let target = Constraint::contradiction();
        assert_eq!(
            check_rup(&target, &db, &[(1, Lit::neg(0))], 2),
            Err(RupError::StepNotPropagating)
        );
    }

    /// ...and a genuine wide propagation still replays.
    #[test]
    fn a_genuine_propagation_beyond_i64_replays() {
        let huge = Big::from(u64::MAX) * Big::from(u64::MAX);
        // 2^128-ish * x >= 1 really does propagate x.
        let c1 = Constraint::new(
            vec![Term {
                coeff: huge.clone(),
                lit: x(),
            }],
            huge.clone(),
        );
        let c2 = Constraint::new(
            vec![Term {
                coeff: Big::from(1),
                lit: x().negate(),
            }],
            Big::from(1),
        );
        let db = [&c1, &c2];
        let target = Constraint::contradiction();
        assert_eq!(check_rup(&target, &db, &[(1, x())], 2), Ok(()));
    }

    /// A tiny deterministic xorshift PRNG, in the style of `normalize.rs`'s
    /// equivalence test, so this needs no dependencies and reproduces exactly.
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut s = self.0;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            self.0 = s;
            s
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    #[test]
    fn indexed_replay_matches_the_naive_fold_on_randomized_certificates() {
        let mut rng = XorShift(0x1234_5678_9abc_def0);
        let mut accepts = 0usize;
        for case in 0..20_000 {
            // Few variables and narrow constraints, so trails actually
            // propagate and conflicts actually happen; duplicate literals and
            // negative coefficients are generated on purpose, since those are
            // exactly where a naive "subtract the coefficient" shortcut would
            // part company with `slackWithout`.
            let var_range = 1 + rng.below(4) as u32;
            let mut owned: Vec<Constraint> = Vec::new();
            let n_c = 1 + rng.below(4) as usize;
            for _ in 0..n_c {
                let width = rng.below(5) as usize;
                let terms: Vec<Term> = (0..width)
                    .map(|_| {
                        let var = rng.below(u64::from(var_range)) as u32;
                        let lit = if rng.below(2) == 0 {
                            Lit::pos(var)
                        } else {
                            Lit::neg(var)
                        };
                        let coeff = match rng.below(12) {
                            0 => -(rng.below(3) as i64) - 1,
                            _ => rng.below(4) as i64,
                        };
                        Term { coeff, lit }
                    })
                    .collect();
                let degree = rng.below(5) as i64 - 1;
                owned.push(Constraint::new(terms, degree));
            }
            let db: Vec<&Constraint> = owned.iter().collect();
            let target = {
                let width = rng.below(3) as usize;
                let terms: Vec<Term> = (0..width)
                    .map(|_| {
                        let var = rng.below(u64::from(var_range)) as u32;
                        let lit = if rng.below(2) == 0 {
                            Lit::pos(var)
                        } else {
                            Lit::neg(var)
                        };
                        Term {
                            coeff: rng.below(3) as i64,
                            lit,
                        }
                    })
                    .collect();
                Constraint::new(terms, rng.below(3) as i64)
            };
            let n_steps = rng.below(6) as usize;
            let steps: Vec<(usize, Lit)> = (0..n_steps)
                .map(|_| {
                    // Deliberately includes out-of-range indices and repeated
                    // literals, including literals already falsified.
                    let i = rng.below(db.len() as u64 + 2) as usize;
                    let var = rng.below(u64::from(var_range)) as u32;
                    let lit = if rng.below(2) == 0 {
                        Lit::pos(var)
                    } else {
                        Lit::neg(var)
                    };
                    (i, lit)
                })
                .collect();
            let conflict = rng.below(db.len() as u64 + 2) as usize;

            let naive = check_rup_dispatch(&target, &db, &steps, conflict, false);
            let indexed = check_rup_dispatch(&target, &db, &steps, conflict, true);
            assert_eq!(
                naive, indexed,
                "case {case}: target {target:?} db {owned:?} steps {steps:?} conflict {conflict}"
            );

            // The identical certificate at the complete domain must reach the
            // identical verdict: the two instantiations run one replay, and
            // nothing about it may depend on the storage width.
            let widen = |c: &Constraint| {
                Constraint::new(
                    c.terms
                        .iter()
                        .map(|t| Term {
                            coeff: Big::from(t.coeff),
                            lit: t.lit,
                        })
                        .collect(),
                    Big::from(c.degree),
                )
            };
            let wide_owned: Vec<Constraint<Big>> = owned.iter().map(widen).collect();
            let wide_db: Vec<&Constraint<Big>> = wide_owned.iter().collect();
            assert_eq!(
                check_rup(&widen(&target), &wide_db, &steps, conflict),
                naive,
                "case {case}: the two instantiations disagreed"
            );

            if naive.is_ok() {
                accepts += 1;
            }
        }
        // The generator must actually reach the accepting path, or the test
        // would pass by rejecting everything through the same early exits.
        assert!(
            accepts > 100,
            "only {accepts} accepting certificates generated"
        );
    }

    #[test]
    fn the_index_gate_does_not_change_the_verdict_on_a_wide_replay() {
        // One 400-term row propagating every one of its literals: the shape
        // the index exists for, and past the dispatch threshold.
        let width = 400u32;
        let terms: Vec<Term> = (0..width)
            .map(|v| Term {
                coeff: 1,
                lit: Lit::pos(v),
            })
            .collect();
        let wide = Constraint::new(terms, i64::from(width));
        let blocker = Constraint::new(
            vec![Term {
                coeff: 1,
                lit: Lit::neg(0),
            }],
            1,
        );
        let db = [&wide, &blocker];
        let target = Constraint::contradiction();
        let steps: Vec<(usize, Lit)> = (0..width).map(|v| (1usize, Lit::pos(v))).collect();
        assert!(use_slack_index(target.terms.len(), &db, &steps, 2));
        assert_eq!(check_rup_dispatch(&target, &db, &steps, 2, true), Ok(()));
        assert_eq!(check_rup_dispatch(&target, &db, &steps, 2, false), Ok(()));
    }

    #[test]
    fn rup_of_entailed_constraint_uses_own_negation() {
        // DB = [x >= 1]; target x >= 1. Negation is ~x >= 1 (index 0), which
        // propagates ~x; then constraint 1 (x >= 1) conflicts.
        let c1 = unit(x());
        let db = [&c1];
        assert_eq!(check_rup(&c1, &db, &[(0, x().negate())], 1), Ok(()));
    }
}
