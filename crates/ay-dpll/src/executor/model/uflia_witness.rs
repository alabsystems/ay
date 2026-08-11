// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #uflia-witness-complete — model-EXTRACTION completion for the QF_UFLIA
//! model-rejection tail (`AY_UFLIA_WITNESS_COMPLETE=1`, default OFF and
//! byte-identical: every entry point is a single `OnceLock`-cached `var`
//! probe taken before any state is read or written).
//!
//! CENSUS. Of the 70 QF_UFLIA sat misses at `-T:20`, 17 are MODEL-REJECTION:
//! a candidate model is built at a median 2.0s of the 20s budget, a gate
//! correctly refutes it, and the blind congruence-repair re-solve then burns
//! ~90% of the budget and fails. Two sub-classes are mechanically diagnosed,
//! and both are EXTRACTION gaps — the search point is fine, the extracted
//! witness is under-specified:
//!
//! (1a) SENTINEL-POISONED EXTRACTION. UFLIA extraction ships NO arithmetic
//!      value for range-bounded Int leaves, so they take the absent-value
//!      default (0) and collide on an asserted `(not (= xi xj))`. The
//!      `#qf-auflia-diseq-shift` repair in `repair_asserted_array_read_pins`
//!      then moves one side to a FRESH sentinel (`1_000_003+`) with no regard
//!      for the `(< xi N)` asserted in the same formula, and the strict
//!      arithmetic oracle definitively refutes the result. The in-code
//!      justification "shifting one side to a fresh integer can only help" is
//!      FALSE whenever the variable carries asserted bounds. Both halves are
//!      fixed here: [`Executor::uflia_fill_bounded_int_leaves`] gives every
//!      absent bound-carrying Int leaf a value INSIDE its asserted interval
//!      (distinct from its asserted-disequality peers), and
//!      [`Executor::uflia_bounded_diseq_shift_value`] makes the shift itself
//!      range-aware — it REFUSES to move a bound-carrying variable at all
//!      (`AY_UFLIA_WITNESS_SHIFT=inrange` confines it to the interval
//!      instead; see that function for why refusal is the measured default).
//!
//! (1b) UNDER-COMPLETED UF TABLE. The gate refutes at a LEGAL x-point (in
//!      range, pairwise distinct) at which the formula IS satisfiable: the
//!      chain argument `(ite (< (+ x1 xk) N) (+ x1 xk) x1)` evaluates to the
//!      one integer in `[0,N)` OUTSIDE `{x1..xn}`, a point where the hash is
//!      applied nowhere else and is therefore COMPLETELY FREE. The extracted
//!      EUF table simply did not pick the colliding value.
//!      [`Executor::uflia_complete_free_uf_chain_witness`] repairs this in two
//!      passes under ONE gate-verified retraction:
//!      [`Executor::uflia_repair_uf_injections`] first completes each
//!      function's PRIMARY domain (the asserted pairwise-distinct `f(x_i)`
//!      group, whose absent values all collapsed onto the default), then the
//!      chain pass verifies the free-point condition — the argument value
//!      occurs at NO other application of that function anywhere in the
//!      formula — and continues the free side from the other side's CANONICAL
//!      value, so the innermost level is the only genuinely free choice and
//!      every outer level is FORCED by congruence.
//!
//! SOUNDNESS IS STRUCTURAL, NOT ANALYTIC — three independent reasons, any one
//! of which suffices:
//!
//! 1. GATE-VERIFIED INSTALL. A completion is only written into the model when
//!    the UNCHANGED strict definitive-false oracle AND the UNCHANGED
//!    independent fail-closed gate both accept the completed witness. Anything
//!    else restores the pre-completion model byte-for-byte, including its
//!    validation-evidence flag, so a non-converting completion is a NO-OP on
//!    the verdict path.
//! 2. RE-VALIDATION. On acceptance the validation-evidence flag is CLEARED, so
//!    the caller (`apply_strict_model_gate` / an in-loop
//!    `finalize_sat_model_validation`) re-runs the full validation pipeline
//!    over the COMPLETED witness rather than trusting stale evidence.
//! 3. THE CHOKEPOINT. Both entry points sit BEFORE the strict oracle, and every
//!    public SAT still leaves through `emit_sat_verdict` — strict, independent,
//!    authoritative-failclosed, non-string-seq, quantified, and the
//!    `last_model_validated` emission postcondition, all UNCHANGED.
//!
//! So a completion that is wrong anywhere is refuted by exactly the gates that
//! refute an unrepaired model today, and the verdict degrades to `unknown`. No
//! gate is weakened, no verdict path reads a flag set here, and nothing here
//! can turn a refutation into an acceptance except by making the witness
//! genuinely satisfy the assertion the gate re-checks.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::{EvalValue, Model};
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// Env gate. Default off; every site below is behind it, so unset is
/// byte-identical (no scan, no clone, no model mutation).
pub(crate) fn uflia_witness_complete_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_UFLIA_WITNESS_COMPLETE").ok().as_deref() == Some("1"))
}

fn debug_enabled() -> bool {
    std::env::var_os("AY_UFLIA_WITNESS_DEBUG").is_some()
}

/// Per-half A/B selector, so the orchestrator (and a bisect) can attribute a
/// conversion or a regression to the SENTINEL half (1a) or the FREE-POINT half
/// (1b) without a rebuild. `AY_UFLIA_WITNESS_PARTS=fill` / `=chain`; unset (or
/// any other value) means BOTH, which is what the main gate enables.
fn part_enabled(part: &str) -> bool {
    if !uflia_witness_complete_enabled() {
        return false;
    }
    static PARTS: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    match PARTS
        .get_or_init(|| std::env::var("AY_UFLIA_WITNESS_PARTS").ok())
        .as_deref()
    {
        Some("fill") => part == "fill",
        Some("chain") => part == "chain",
        _ => true,
    }
}

/// Conjunct-window fence for the chain sweep. The target family carries a few
/// thousand conjuncts and the per-conjunct test is a shallow syntactic match,
/// but an adversarial window must not turn completion into its own spin.
const MAX_FLAT_CONJUNCTS: usize = 32_768;
/// Fence on the UF-application index walk (one pass over the assertion DAG).
const MAX_WALK_NODES: usize = 500_000;
/// Longest UF chain considered on either side of a candidate equality.
const MAX_CHAIN_DEPTH: usize = 16;
/// Largest disjunction admitted as an injection-completion authority source.
const MAX_OR_DISJUNCTS: usize = 1_024;
/// Traversal fence for a nested allowed-value disjunction.
const MAX_OR_WALK_NODES: usize = 4_096;
/// Fence on the bounded-leaf repair: the number of range-carrying Int leaves.
const MAX_BOUNDED_LEAVES: usize = 4_096;
/// Widest asserted interval the bounded-leaf repair will search for a free
/// value. The target family's intervals are `[0, n+1)`; a huge interval means
/// the "collision" is not a finite-domain packing problem at all.
const MAX_BOUNDED_INTERVAL: u64 = 4_096;

/// An asserted constant range `lo <= x < hi` on an Int leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::executor) struct AssertedRange {
    pub(in crate::executor) lo: BigInt,
    /// EXCLUSIVE upper bound.
    pub(in crate::executor) hi: BigInt,
}

impl Executor {
    /// Index the asserted constant range bounds of Int leaves.
    ///
    /// One pass over the flattened assertion window collecting the atoms
    /// `(<= c x)` / `(< c x)` / `(>= x c)` / `(> x c)` (lower) and
    /// `(< x c)` / `(<= x c)` / `(> c x)` / `(>= c x)` (upper) for a LEAF `x`
    /// (declared variable or nullary application) and an integer LITERAL `c`.
    /// Only leaves with BOTH a lower and an upper bound and a non-empty
    /// interval are returned: those are the variables for which "shift to a
    /// fresh integer" is provably wrong.
    ///
    /// Read-only; it never inspects or touches the model.
    pub(in crate::executor) fn asserted_int_ranges(&self) -> DetHashMap<TermId, AssertedRange> {
        let mut lows: DetHashMap<TermId, BigInt> = DetHashMap::default();
        let mut highs: DetHashMap<TermId, BigInt> = DetHashMap::default();
        let flat = self.flatten_assertion_conjunctions();
        if flat.len() > MAX_FLAT_CONJUNCTS {
            return DetHashMap::default();
        }
        for assertion in flat {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (a, b) = (args[0], args[1]);
            let op = sym.name();
            if !matches!(op, "<" | "<=" | ">" | ">=") {
                continue;
            }
            // Normalize to `left op right` with exactly one literal side.
            let (leaf, lit, leaf_on_left) = match (
                self.int_literal(a),
                self.int_literal(b),
                self.is_int_leaf(a),
                self.is_int_leaf(b),
            ) {
                (None, Some(c), true, _) => (a, c, true),
                (Some(c), None, _, true) => (b, c, false),
                _ => continue,
            };
            // `leaf op lit` (leaf_on_left) or `lit op leaf`.
            let (bound, is_lower) = match (op, leaf_on_left) {
                (">=", true) | ("<=", false) => (lit, true),
                (">", true) | ("<", false) => (lit + 1, true),
                ("<", true) | (">", false) => (lit, false),
                ("<=", true) | (">=", false) => (lit + 1, false),
                _ => continue,
            };
            if is_lower {
                lows.entry(leaf)
                    .and_modify(|cur| {
                        if bound > *cur {
                            *cur = bound.clone();
                        }
                    })
                    .or_insert(bound);
            } else {
                highs
                    .entry(leaf)
                    .and_modify(|cur| {
                        if bound < *cur {
                            *cur = bound.clone();
                        }
                    })
                    .or_insert(bound);
            }
        }
        let mut out: DetHashMap<TermId, AssertedRange> = DetHashMap::default();
        for (leaf, lo) in lows {
            let Some(hi) = highs.get(&leaf) else { continue };
            if &lo >= hi {
                continue;
            }
            out.insert(leaf, AssertedRange { lo, hi: hi.clone() });
        }
        out
    }

    fn int_literal(&self, t: TermId) -> Option<BigInt> {
        match self.ctx.terms.get(t) {
            TermData::Const(ay_core::term::Constant::Int(v)) => Some(v.clone()),
            _ => None,
        }
    }

    fn is_int_leaf(&self, t: TermId) -> bool {
        matches!(self.ctx.terms.sort(t), Sort::Int)
            && match self.ctx.terms.get(t) {
                TermData::Var(_, _) => true,
                TermData::App(_, args) => args.is_empty(),
                _ => false,
            }
    }

    /// Index the asserted var-var Int DISEQUALITY peers of every Int leaf:
    /// `(not (= x y))` (which is how `distinct` over a pair normalizes).
    pub(in crate::executor) fn asserted_int_diseq_peers(&self) -> DetHashMap<TermId, Vec<TermId>> {
        let mut out: DetHashMap<TermId, Vec<TermId>> = DetHashMap::default();
        let flat = self.flatten_assertion_conjunctions();
        if flat.len() > MAX_FLAT_CONJUNCTS {
            return out;
        }
        for assertion in flat {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                continue;
            };
            let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (x, y) = (args[0], args[1]);
            if !self.is_int_leaf(x) || !self.is_int_leaf(y) {
                continue;
            }
            out.entry(x).or_default().push(y);
            out.entry(y).or_default().push(x);
        }
        out
    }

    fn model_int_value(&self, model: &Model, t: TermId) -> Option<BigInt> {
        match self.evaluate_term(model, t) {
            EvalValue::Rational(r) if r.is_integer() => Some(r.numer().clone()),
            _ => None,
        }
    }

    /// (1a-i) Give every ASSERTED-BOUND Int leaf a value INSIDE its asserted
    /// interval, distinct from the values its asserted-disequality peers hold.
    ///
    /// Extraction routinely ships no arithmetic value at all for these leaves
    /// (they appear only under UF applications, so LIA never rows them); they
    /// then take the absent-value default 0, several collide, and the
    /// range-blind diseq shift moves one of them out of bounds. Filling them
    /// in-range up front removes the collision at its source.
    ///
    /// FILL/CORRECT ONLY, CANDIDATE ONLY: a leaf the model already values
    /// INSIDE its interval is never touched (see the in-body note — re-seating
    /// a live value re-keys the extracted UF tables), and every gate still
    /// decides acceptance. Returns the number of leaves whose value changed.
    pub(in crate::executor) fn uflia_fill_bounded_int_leaves(&mut self) -> usize {
        if !part_enabled("fill") {
            return 0;
        }
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return 0;
        }
        let ranges = self.asserted_int_ranges();
        if debug_enabled() {
            eprintln!(
                "[uflia-witness] bounded-leaf entry: {} range-carrying Int leaves",
                ranges.len()
            );
        }
        if ranges.is_empty() || ranges.len() > MAX_BOUNDED_LEAVES {
            return 0;
        }
        let peers = self.asserted_int_diseq_peers();
        let Some(mut model) = self.last_model.take() else {
            return 0;
        };
        // Deterministic order: TermId.
        let mut leaves: Vec<TermId> = ranges.keys().copied().collect();
        leaves.sort_by_key(|t| t.0);

        // Current values (absent leaves are simply unvalued here — the 0
        // default the downstream evaluator applies is exactly the collision
        // this pass removes).
        let mut values: DetHashMap<TermId, BigInt> = DetHashMap::default();
        for &leaf in &leaves {
            if let Some(v) = self.model_int_value(&model, leaf) {
                values.insert(leaf, v);
            }
        }
        let mut fixed = 0usize;
        let mut assignments: Vec<(TermId, BigInt)> = Vec::new();
        for &leaf in &leaves {
            let range = &ranges[&leaf];
            if (&range.hi - &range.lo) > BigInt::from(MAX_BOUNDED_INTERVAL) {
                continue;
            }
            let peer_values: DetHashSet<BigInt> = peers
                .get(&leaf)
                .map(|ps| {
                    ps.iter()
                        .filter(|p| **p != leaf)
                        .filter_map(|p| values.get(p).cloned())
                        .collect()
                })
                .unwrap_or_default();
            let current = values.get(&leaf).cloned();
            // FILL-ONLY, plus out-of-interval CORRECTION. A leaf the model
            // already values INSIDE its interval is never moved, even when it
            // collides with a peer: every UF function-table row keyed by that
            // leaf moves with it, so re-seating a live value silently re-keys
            // the whole extracted witness (measured on `hash_sat_07_07`:
            // re-seating `x1` from a live `0` to `3` collapsed five `hash_1`
            // rows onto one argument point and turned a genuine sat into
            // unknown). A collision between two LIVE in-interval values is
            // left to the gates, which refute it on the asserted disequality
            // exactly as they do today. This pass exists only for the values
            // extraction never produced — and for a value already outside the
            // asserted interval, which every arithmetic oracle refutes anyway,
            // so moving it in-range can only help.
            let out_of_interval = current
                .as_ref()
                .is_some_and(|v| v < &range.lo || v >= &range.hi);
            if current.is_some() && !out_of_interval {
                continue;
            }
            // Smallest in-interval value no asserted-distinct peer holds.
            let mut candidate = range.lo.clone();
            let mut chosen = None;
            while candidate < range.hi {
                if !peer_values.contains(&candidate) {
                    chosen = Some(candidate.clone());
                    break;
                }
                candidate += 1;
            }
            let Some(chosen) = chosen else { continue };
            if current.as_ref() == Some(&chosen) {
                continue;
            }
            if debug_enabled() {
                eprintln!(
                    "[uflia-witness] bounded-leaf {} := {} (was {:?}, range [{}, {}))",
                    self.format_term(leaf),
                    chosen,
                    current,
                    range.lo,
                    range.hi
                );
            }
            values.insert(leaf, chosen.clone());
            assignments.push((leaf, chosen));
            fixed += 1;
        }
        for (leaf, value) in assignments {
            self.pin_int_leaf_value(&mut model, leaf, &value);
        }
        if fixed > 0 {
            model.revoke_cegqi_uf_recompletion();
            self.cegqi_uf_recompletion_grant = None;
            self.last_model_validated = false;
            self.last_statistics
                .set_int("uflia_witness.bounded_leaves_filled", fixed as u64);
        }
        self.last_model = Some(model);
        fixed
    }

    /// (1a-ii) The value the `#qf-auflia-diseq-shift` repair may move `target`
    /// to.
    ///
    /// When `target` carries NO asserted range bounds the caller's fresh
    /// sentinel is returned unchanged (historic behaviour). When it DOES, the
    /// sentinel is provably wrong — it falsifies the very `(< target N)` the
    /// same formula asserts — so the shift is confined to the asserted
    /// interval: the smallest in-interval value no asserted-distinct peer
    /// currently holds. `None` means REFUSE to shift (the caller leaves the
    /// model untouched and the gates reject it exactly as they do today).
    pub(in crate::executor) fn uflia_bounded_diseq_shift_value(
        &self,
        model: &Model,
        ranges: &DetHashMap<TermId, AssertedRange>,
        peers: &DetHashMap<TermId, Vec<TermId>>,
        target: TermId,
        fresh: i64,
    ) -> Option<i64> {
        if !part_enabled("fill") {
            return Some(fresh);
        }
        let Some(range) = ranges.get(&target) else {
            return Some(fresh);
        };
        if (&range.hi - &range.lo) > BigInt::from(MAX_BOUNDED_INTERVAL) {
            return Some(fresh);
        }
        let peer_values: DetHashSet<BigInt> = peers
            .get(&target)
            .map(|ps| {
                ps.iter()
                    .filter(|p| **p != target)
                    .filter_map(|p| self.model_int_value(model, *p))
                    .collect()
            })
            .unwrap_or_default();
        // DEFAULT: REFUSE. Both of the task's options were measured on the
        // mathsat Hash tail and they are NOT equivalent.
        //
        // * REFUSE leaves the witness exactly as extraction produced it. The
        //   collision `(= x_i x_j)` still falsifies the asserted disequality,
        //   so the strict oracle refutes this candidate and the search moves
        //   on — the SAME outcome the sentinel produced (it, too, was always
        //   refuted, just on `(< x_i N)` instead), minus the out-of-bounds
        //   value that made the rejection look like an arithmetic bug.
        // * SHIFT-IN-RANGE invents a value the extracted UF tables were never
        //   keyed by. That candidate can then survive the strict oracle and
        //   die later at the independent gate, burning the remnant budget on
        //   a witness whose function graph no longer matches its own domain
        //   points (measured deterministic sat->unknown on `hash_sat_07_07`
        //   and `hash_sat_07_20`, 3/3 runs each).
        //
        // `AY_UFLIA_WITNESS_SHIFT=inrange` selects the second behaviour for
        // A/B; anything else (including unset) refuses.
        static IN_RANGE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let in_range = *IN_RANGE.get_or_init(|| {
            std::env::var("AY_UFLIA_WITNESS_SHIFT").ok().as_deref() == Some("inrange")
        });
        if in_range {
            let mut candidate = range.lo.clone();
            while candidate < range.hi {
                if !peer_values.contains(&candidate) {
                    return i64::try_from(candidate).ok();
                }
                candidate += 1;
            }
        }
        if debug_enabled() {
            eprintln!(
                "[uflia-witness] diseq-shift REFUSED for {} (asserted range [{}, {}) \
                 forbids the fresh sentinel)",
                self.format_term(target),
                range.lo,
                range.hi
            );
        }
        None
    }

    /// (1b) Complete a falsified UF-chain equality through a FREE function
    /// point.
    ///
    /// Returns `true` when the model was changed. See the module docs for the
    /// class; the soundness argument is that the caller runs this BEFORE the
    /// strict oracle, so every unchanged gate re-checks the completed witness.
    pub(in crate::executor) fn uflia_complete_free_uf_chain_witness(&mut self) -> bool {
        if !part_enabled("chain") {
            return false;
        }
        if !matches!(self.last_result, Some(SolveResult::Sat)) {
            return false;
        }
        if debug_enabled() {
            eprintln!(
                "[uflia-witness] free-chain entry: model={}",
                self.last_model.is_some()
            );
        }
        let Some(mut model) = self.last_model.take() else {
            return false;
        };
        if model.euf_model.is_none() {
            self.last_model = Some(model);
            return false;
        }
        // GATE-VERIFIED, RETRACTING (the same discipline as
        // `complete_string_gaps_gate_verified` / `complete_constrained_gaps`).
        // Keep the pre-completion witness; install the completed one ONLY when
        // the UNCHANGED strict definitive-false oracle AND the UNCHANGED
        // independent fail-closed gate both accept it. Otherwise restore the
        // snapshot byte-for-byte, including the validation-evidence flag, so a
        // completion that does not convert is a NO-OP on the verdict path.
        //
        // Without this the completion is applied to every candidate a chain
        // equality can be found in — including models that are broken for
        // unrelated reasons — and merely re-shapes a rejection that was going
        // to happen anyway, at the cost of the whole downstream pipeline
        // re-running (measured: two sat->unknown regressions on
        // `hash_sat_07_07` / `hash_sat_07_20`, both models refuted on OTHER
        // conjuncts). Retracting makes the lever strictly recover-only.
        let snapshot = model.clone();
        let saved_validated = self.last_model_validated;
        // Two completion passes under ONE retraction. The injection repair runs
        // FIRST: it fixes the PRIMARY domain points (`f(x_i)`), which is what
        // the chain completion then reads its canonical graphs from.
        let mut changed = self.uflia_repair_uf_injections(&mut model);
        changed |= self.uflia_try_free_chain_completion(&mut model);
        self.last_model = Some(model);
        if !changed {
            return false;
        }
        // CACHE ISOLATION. `IndependentModelView`'s resolution caches and the
        // `evaluate_term` memo are keyed by TermId alone, on the assumption
        // that model and assertion set are FIXED for the lifetime of the scope
        // (`GateViewCacheSession`'s safety contract). This verification runs
        // over a DIFFERENT (completed) model than the one the funnel's own gate
        // sequence will read if we retract, so it must own its scope and leave
        // no residue — otherwise gate (2) in `emit_sat_verdict` reads values
        // computed under the retracted witness (measured: this alone regressed
        // `hash_sat_07_07` / `hash_sat_07_20` from sat to unknown even though
        // the completion itself was retracted).
        let accepted = {
            let _view_caches = super::independent_gate::GateViewCacheSession::new();
            let _eval_memo = super::EvalMemoSession::new();
            self.verify_model_strict().is_none()
                && matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ConfirmedSat
                )
        };
        super::eval_memo_clear();
        if !accepted {
            if debug_enabled() {
                eprintln!("[uflia-witness] completion RETRACTED (gates did not confirm)");
            }
            self.last_model = Some(snapshot);
            self.last_model_validated = saved_validated;
            self.last_statistics
                .set_int("uflia_witness.completion_retracted", 1);
            return false;
        }
        // Accepted. The witness was MUTATED, so any prior validation evidence
        // is stale: clear it and let `emit_sat_verdict` re-run the full
        // unchanged pipeline over the completed model before any certificate
        // can be minted (#7912 postcondition).
        self.last_model_validated = false;
        self.revoke_cegqi_uf_recompletion_authority();
        self.last_statistics
            .set_int("uflia_witness.free_uf_point_completed", 1);
        true
    }

    /// (1b, primary domain) UNDER-COMPLETED UF TABLE — the DEGENERATE-VALUE
    /// half.
    ///
    /// Extraction can leave several applications of one function with NO value
    /// of their own; they all take the absent-value default, so the extracted
    /// table maps distinct argument points to ONE result and the asserted
    /// `(not (= (f x_i) (f x_j)))` group is violated by the WITNESS even though
    /// the search point is fine (measured on `hash_sat_07_18`: `hash_18` mapped
    /// the three argument points `2`, `3` and `7` all to `0`, and `hash_1`
    /// carried five applications at argument point `0`).
    ///
    /// The formula pins down exactly what a legal completion is:
    ///   * an asserted `(not (= (f a) (f b)))` group means those applications
    ///     are pairwise DISTINCT, and
    ///   * an asserted `(or (= (f a) t1) ... (= (f a) tk))` means `f(a)` is one
    ///     of the evaluated `t_i`.
    /// So the obligation is a partial INJECTION into a finite allowed set.
    /// Keep every value that is already legal and unique, then give each
    /// collapsed / out-of-set application the smallest allowed value nobody
    /// else in its group holds. When no such value exists the repair ABORTS
    /// (nothing is written) — and in any case the caller's gate-verified
    /// retraction is what decides whether the result is installed at all.
    ///
    /// Two applications whose ARGUMENTS evaluate equal are congruent and must
    /// share a value; a disequality group containing such a pair is not
    /// repairable by table completion (it is the 1a leaf-collision class), so
    /// the repair steps aside there.
    fn uflia_repair_uf_injections(&mut self, model: &mut Model) -> bool {
        let unary_ufs = self.plain_unary_uf_names();
        if unary_ufs.is_empty() {
            return false;
        }
        let flat = self.flatten_assertion_conjunctions();
        if flat.is_empty() || flat.len() > MAX_FLAT_CONJUNCTS {
            return false;
        }
        // ONE pass over the window: per head, the asserted distinctness pairs
        // and the asserted allowed-value disjunctions.
        let mut diseq_pairs: DetHashMap<String, Vec<(TermId, TermId)>> = DetHashMap::default();
        let mut allowed_terms: DetHashMap<TermId, Vec<TermId>> = DetHashMap::default();
        for &conjunct in &flat {
            match self.ctx.terms.get(conjunct) {
                TermData::Not(inner) => {
                    let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
                        continue;
                    };
                    if sym.name() != "=" || args.len() != 2 {
                        continue;
                    }
                    let (u, v) = (args[0], args[1]);
                    let (Some(hu), Some(hv)) = (
                        self.unary_uf_head(u, &unary_ufs),
                        self.unary_uf_head(v, &unary_ufs),
                    ) else {
                        continue;
                    };
                    if hu != hv {
                        continue;
                    }
                    diseq_pairs.entry(hu).or_default().push((u, v));
                }
                TermData::App(sym, _) if sym.name() == "or" => {
                    let Some(disjuncts) = self.flatten_or(conjunct) else {
                        // A truncated disjunction is not an authority for the
                        // allowed-value set. Fail closed on either fence.
                        continue;
                    };
                    // Every disjunct must be `(= <the same f-app> t)`.
                    let mut target: Option<TermId> = None;
                    let mut values: Vec<TermId> = Vec::new();
                    let mut ok = true;
                    for d in &disjuncts {
                        let TermData::App(dsym, dargs) = self.ctx.terms.get(*d) else {
                            ok = false;
                            break;
                        };
                        if dsym.name() != "=" || dargs.len() != 2 {
                            ok = false;
                            break;
                        }
                        let (l, r) = (dargs[0], dargs[1]);
                        let (app, value) = match (
                            self.unary_uf_head(l, &unary_ufs).is_some(),
                            self.unary_uf_head(r, &unary_ufs).is_some(),
                        ) {
                            (true, false) => (l, r),
                            (false, true) => (r, l),
                            _ => {
                                ok = false;
                                break;
                            }
                        };
                        if *target.get_or_insert(app) != app {
                            ok = false;
                            break;
                        }
                        values.push(value);
                    }
                    if ok {
                        if let Some(app) = target {
                            allowed_terms.entry(app).or_default().extend(values);
                        }
                    }
                }
                _ => {}
            }
        }
        if diseq_pairs.is_empty() {
            return false;
        }
        let mut changed = false;
        let mut heads: Vec<String> = diseq_pairs.keys().cloned().collect();
        heads.sort();
        for head in heads {
            // A quantified SAT certificate already fixed the complete graph,
            // including its default. It is not a free-point model that this
            // witness-repair pass may extend.
            if model.has_certified_total_uf(&head) {
                continue;
            }
            if model
                .euf_model
                .as_ref()
                .is_some_and(|e| e.function_table_conflicts.contains(&head))
            {
                continue;
            }
            let pairs = diseq_pairs[&head].clone();
            // Members of the distinctness group, deterministic order.
            let mut group: Vec<TermId> = Vec::new();
            for (u, v) in &pairs {
                for t in [*u, *v] {
                    if !group.contains(&t) {
                        group.push(t);
                    }
                }
            }
            group.sort_by_key(|t| t.0);
            if group.len() < 2 || group.len() > MAX_BOUNDED_LEAVES {
                continue;
            }
            // Congruence guard: two group members at the SAME argument point
            // must be equal, so the group is not repairable here.
            let mut arg_seen: DetHashSet<BigInt> = DetHashSet::default();
            let mut congruent_clash = false;
            for &app in &group {
                let TermData::App(_, args) = self.ctx.terms.get(app) else {
                    congruent_clash = true;
                    break;
                };
                let Some(v) = self.model_int_value(model, args[0]) else {
                    congruent_clash = true;
                    break;
                };
                if !arg_seen.insert(v) {
                    congruent_clash = true;
                    break;
                }
            }
            if congruent_clash {
                if debug_enabled() {
                    eprintln!(
                        "[uflia-witness] injection {head}: skipped (argument points not distinct)"
                    );
                }
                continue;
            }
            // Allowed value set per member.
            let mut allowed: Vec<Vec<BigInt>> = Vec::with_capacity(group.len());
            for &app in &group {
                let mut vals: Vec<BigInt> = Vec::new();
                if let Some(terms) = allowed_terms.get(&app) {
                    for &t in terms {
                        if let Some(v) = self.model_int_value(model, t) {
                            if !vals.contains(&v) {
                                vals.push(v);
                            }
                        }
                    }
                }
                vals.sort();
                allowed.push(vals);
            }
            if allowed.iter().all(Vec::is_empty) {
                continue;
            }
            // Keep legal + unique values; collect the rest for reassignment.
            let mut current: Vec<Option<BigInt>> = Vec::with_capacity(group.len());
            let mut used: DetHashSet<BigInt> = DetHashSet::default();
            let mut needs: Vec<usize> = Vec::new();
            for (i, &app) in group.iter().enumerate() {
                let v = self.model_int_value(model, app);
                let legal = v.as_ref().is_some_and(|v| {
                    (allowed[i].is_empty() || allowed[i].contains(v)) && !used.contains(v)
                });
                if legal {
                    used.insert(v.clone().expect("legal implies some"));
                    current.push(v);
                } else {
                    current.push(None);
                    needs.push(i);
                }
            }
            if needs.is_empty() {
                continue;
            }
            // Reassign, smallest allowed value nobody holds. Abort the whole
            // head on failure — a partial injection is no better than none.
            let mut plan: Vec<(TermId, BigInt)> = Vec::new();
            let mut aborted = false;
            for &i in &needs {
                let Some(pick) = allowed[i].iter().find(|v| !used.contains(*v)).cloned() else {
                    aborted = true;
                    break;
                };
                used.insert(pick.clone());
                current[i] = Some(pick.clone());
                plan.push((group[i], pick));
            }
            if aborted {
                if debug_enabled() {
                    eprintln!("[uflia-witness] injection {head}: aborted (no free allowed value)");
                }
                continue;
            }
            if debug_enabled() {
                eprintln!(
                    "[uflia-witness] injection {head}: repaired {} of {} applications",
                    plan.len(),
                    group.len()
                );
            }
            for (app, value) in plan {
                let arg_value = match self.ctx.terms.get(app) {
                    TermData::App(_, args) => self.model_int_value(model, args[0]),
                    _ => None,
                };
                self.pin_int_app_value(model, app, &value);
                if let Some(key) = arg_value {
                    self.add_uf_table_row(model, &head, app, &key, &value);
                }
                changed = true;
            }
        }
        changed
    }

    /// The head name when `t` is a unary application of a plain uninterpreted
    /// function, else `None`.
    fn unary_uf_head(&self, t: TermId, unary_ufs: &DetHashSet<String>) -> Option<String> {
        match self.ctx.terms.get(t) {
            TermData::App(sym, args) if args.len() == 1 && unary_ufs.contains(sym.name()) => {
                Some(sym.name().to_string())
            }
            _ => None,
        }
    }

    /// Flatten a nested `or` into its leaf disjuncts. `None` means a fence was
    /// crossed; callers must not treat a partial prefix as the complete
    /// allowed-value set.
    fn flatten_or(&self, term: TermId) -> Option<Vec<TermId>> {
        self.flatten_or_with_limits(term, MAX_OR_DISJUNCTS, MAX_OR_WALK_NODES)
    }

    fn flatten_or_with_limits(
        &self,
        term: TermId,
        max_disjuncts: usize,
        max_walk_nodes: usize,
    ) -> Option<Vec<TermId>> {
        let mut out = Vec::new();
        let mut stack = vec![term];
        let mut visited = 0usize;
        while let Some(t) = stack.pop() {
            if visited >= max_walk_nodes {
                return None;
            }
            visited += 1;
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "or" => {
                    stack.extend(args.iter().rev().copied());
                }
                _ => {
                    if out.len() >= max_disjuncts {
                        return None;
                    }
                    out.push(t);
                }
            }
        }
        Some(out)
    }

    fn uflia_try_free_chain_completion(&mut self, model: &mut Model) -> bool {
        // Declared unary uninterpreted heads, resolved ONCE. the per-name predicate
        // scans the whole symbol table, so calling it per conjunct would be
        // O(conjuncts x symbols) on every strict-gate pass of every problem.
        let unary_ufs = self.plain_unary_uf_names();
        if unary_ufs.is_empty() {
            return false;
        }
        let flat = self.flatten_assertion_conjunctions();
        if flat.is_empty() || flat.len() > MAX_FLAT_CONJUNCTS {
            return false;
        }
        // Cheap syntactic pre-filter: candidate conjuncts are POSITIVE
        // equalities whose two sides are UF chains with the same head
        // sequence. In the target family there is exactly one.
        let mut candidates: Vec<(
            TermId,
            Vec<(TermId, String, TermId)>,
            Vec<(TermId, String, TermId)>,
        )> = Vec::new();
        for &conjunct in &flat {
            let TermData::App(sym, args) = self.ctx.terms.get(conjunct) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (l, r) = (args[0], args[1]);
            if l == r {
                continue;
            }
            let left = self.uf_unary_chain(l, &unary_ufs);
            let right = self.uf_unary_chain(r, &unary_ufs);
            if left.is_empty() || left.len() != right.len() {
                continue;
            }
            if left
                .iter()
                .zip(&right)
                .any(|((_, lf, _), (_, rf, _))| lf != rf)
            {
                continue;
            }
            candidates.push((conjunct, left, right));
        }
        if debug_enabled() {
            eprintln!(
                "[uflia-witness] chain sweep: {} conjuncts, {} chain-equality candidates",
                flat.len(),
                candidates.len()
            );
        }
        if candidates.is_empty() {
            return false;
        }
        // The free-point argument is authoritative only over a COMPLETE index.
        // A partial walk could hide another application at the alleged free
        // argument, so crossing the fence disables this completion entirely.
        let Some(index) = self.unary_uf_application_index(&unary_ufs) else {
            if debug_enabled() {
                eprintln!("[uflia-witness] chain sweep skipped: application index overflow");
            }
            return false;
        };
        for (conjunct, left, right) in candidates {
            if debug_enabled() {
                let verdict = self.evaluate_term(model, conjunct);
                eprintln!("[uflia-witness] candidate verdict {verdict:?}");
                for (side, chain) in [("L", &left), ("R", &right)] {
                    for (t, f, a) in chain {
                        eprintln!(
                            "  {side} {f}(arg={:?}) = {:?}",
                            self.model_int_value(model, *a),
                            self.model_int_value(model, *t)
                        );
                    }
                }
                for (_, f, _) in left.iter() {
                    if let Some(sites) = index.get(f) {
                        let mut rows: Vec<String> = sites
                            .iter()
                            .map(|(app, arg)| {
                                format!(
                                    "{:?}->{:?}",
                                    self.model_int_value(model, *arg),
                                    self.model_int_value(model, *app)
                                )
                            })
                            .collect();
                        rows.sort();
                        eprintln!("  graph {f}: {}", rows.join(" "));
                    }
                }
            }
            // No `evaluate_term`-based falsity precondition: the class this
            // targets is a model the SOLVER-SIDE evaluator computes TRUE (each
            // chain application carries its own committed value) while the
            // INDEPENDENT gate — which keys applications by their evaluated
            // argument values and takes the FIRST committed value per key —
            // computes FALSE, because the derived chain applications disagree
            // with the primary `f(x_i)` commitments at the same point.
            // Screening on `Bool(false)` here would therefore skip exactly the
            // rejections this exists to repair. `complete_one_chain` reports
            // whether it changed anything, and it changes nothing when the
            // chain is already congruent and equal.
            if self.complete_one_chain(model, &left, &right, &index) {
                return true;
            }
        }
        false
    }

    /// Decompose `t` into its UNARY uninterpreted-function chain, OUTERMOST
    /// first: `[(f(g(a)), "f", g(a)), (g(a), "g", a)]`. Stops as soon as the
    /// argument is not itself a unary uninterpreted application.
    fn uf_unary_chain(
        &self,
        t: TermId,
        unary_ufs: &DetHashSet<String>,
    ) -> Vec<(TermId, String, TermId)> {
        let mut out = Vec::new();
        let mut cur = t;
        while out.len() < MAX_CHAIN_DEPTH {
            let TermData::App(sym, args) = self.ctx.terms.get(cur) else {
                break;
            };
            if args.len() != 1 || !unary_ufs.contains(sym.name()) {
                break;
            }
            let arg = args[0];
            out.push((cur, sym.name().to_string(), arg));
            cur = arg;
        }
        out
    }

    /// Every declared unary uninterpreted function name, resolved once.
    /// Resolving a single name means scanning the whole symbol table, so the
    /// chain walk must never ask per conjunct.
    fn plain_unary_uf_names(&self) -> DetHashSet<String> {
        let mut out: DetHashSet<String> = DetHashSet::default();
        for (name, info) in self.ctx.symbol_iter() {
            if info.arg_sorts.len() != 1 {
                continue;
            }
            if name.starts_with("__ay") || name.starts_with('@') {
                continue;
            }
            if Self::is_known_theory_symbol(name) {
                continue;
            }
            if self.ctx.is_constructor(name).is_some() {
                continue;
            }
            out.insert(name.clone());
        }
        out
    }

    /// Index every unary uninterpreted application reachable from the
    /// assertion window, keyed by head name. Used for the FREE-POINT test:
    /// a function point is free exactly when no OTHER application of that
    /// function anywhere in the formula shares its argument value.
    fn unary_uf_application_index(
        &self,
        unary_ufs: &DetHashSet<String>,
    ) -> Option<DetHashMap<String, Vec<(TermId, TermId)>>> {
        self.unary_uf_application_index_with_limit(unary_ufs, MAX_WALK_NODES)
    }

    fn unary_uf_application_index_with_limit(
        &self,
        unary_ufs: &DetHashSet<String>,
        max_walk_nodes: usize,
    ) -> Option<DetHashMap<String, Vec<(TermId, TermId)>>> {
        let mut out: DetHashMap<String, Vec<(TermId, TermId)>> = DetHashMap::default();
        let mut seen: DetHashSet<TermId> = DetHashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = 0usize;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if visited >= max_walk_nodes {
                return None;
            }
            visited += 1;
            if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                if args.len() == 1 && unary_ufs.contains(sym.name()) {
                    out.entry(sym.name().to_string())
                        .or_default()
                        .push((t, args[0]));
                }
            }
            stack.extend(self.ctx.terms.children(t));
        }
        Some(out)
    }

    /// The CANONICAL function graph of a unary UF as the independent gate
    /// sees it: argument VALUE -> result value, first application site (by
    /// `TermId`, i.e. earliest-created — the primary `f(x_i)` domain points
    /// precede any derived chain application) wins.
    ///
    /// The gate keys applications by their evaluated argument values and takes
    /// the FIRST committed value per key as the single value of the function
    /// there — exactly so that a model pinning two congruent applications to
    /// DIFFERENT values is exposed rather than hidden. Extraction routinely
    /// produces such a model on this family (measured on `hash_sat_08_13`:
    /// `hash_1` committed to `1` at the primary site `hash_1(x8)`, `x8 = 7`,
    /// and to `5` at the derived chain application whose argument also
    /// evaluates to `7`). Rebuilding the graph here is what lets the
    /// completion below reason in the SAME terms the gate will judge it in.
    fn canonical_uf_graph(
        &self,
        model: &Model,
        head: &str,
        apps: &DetHashMap<String, Vec<(TermId, TermId)>>,
    ) -> std::collections::BTreeMap<BigInt, BigInt> {
        let mut graph = std::collections::BTreeMap::new();
        let Some(sites) = apps.get(head) else {
            return graph;
        };
        let mut ordered: Vec<(TermId, TermId)> = sites.clone();
        ordered.sort_by_key(|(app, _)| app.0);
        for (app, arg) in ordered {
            let (Some(key), Some(value)) = (
                self.model_int_value(model, arg),
                self.model_int_value(model, app),
            ) else {
                continue;
            };
            graph.entry(key).or_insert(value);
        }
        graph
    }

    /// Try to complete ONE UF-chain equality through a FREE function point.
    /// `left`/`right` are outermost-first chains with identical head sequences.
    ///
    /// The completion is computed ENTIRELY before any mutation and is applied
    /// only when it makes the conjunct hold; otherwise the model is left
    /// byte-identical.
    fn complete_one_chain(
        &mut self,
        model: &mut Model,
        left: &[(TermId, String, TermId)],
        right: &[(TermId, String, TermId)],
        apps: &DetHashMap<String, Vec<(TermId, TermId)>>,
    ) -> bool {
        let depth = left.len() - 1;
        let (l_app, head, l_arg) = &left[depth];
        let (r_app, _, r_arg) = &right[depth];
        if !matches!(self.ctx.terms.sort(*l_app), Sort::Int) {
            return false;
        }
        // A conflicted table is deliberately opaque to every consumer; never
        // add a row to one. Likewise, a certificate-constructed total table is
        // immutable: changing any chain head would invalidate the certificate
        // and could change the output layer's else row.
        if left.iter().any(|(_, f, _)| {
            model.has_certified_total_uf(f)
                || model
                    .euf_model
                    .as_ref()
                    .is_some_and(|e| e.function_table_conflicts.contains(f))
        }) {
            return false;
        }
        let (Some(l_val), Some(r_val)) = (
            self.model_int_value(model, *l_arg),
            self.model_int_value(model, *r_arg),
        ) else {
            return false;
        };
        if l_val == r_val {
            // Same argument POINT: the two sides are congruent already; a
            // disagreement there is a table inconsistency, not a free point.
            return false;
        }
        let Some(sites) = apps.get(head) else {
            return false;
        };
        // FREE-POINT TEST: the function is applied at this argument VALUE
        // nowhere else in the whole formula, so its value there is
        // unconstrained and may be chosen to satisfy the conjunct.
        let occurrences = |exec: &Self, model: &Model, value: &BigInt| -> usize {
            sites
                .iter()
                .filter(|(_, arg)| exec.model_int_value(model, *arg).as_ref() == Some(value))
                .count()
        };
        let (free, other, free_key, other_key) = if occurrences(self, model, &l_val) <= 1 {
            (left, right, l_val.clone(), r_val.clone())
        } else if occurrences(self, model, &r_val) <= 1 {
            (right, left, r_val.clone(), l_val.clone())
        } else {
            if debug_enabled() {
                eprintln!(
                    "[uflia-witness] chain {head}: neither argument point is free \
                     (l={l_val}, r={r_val})"
                );
            }
            return false;
        };
        // Canonical graphs of every head in the chain, as the gate sees them.
        let mut graphs: Vec<std::collections::BTreeMap<BigInt, BigInt>> =
            Vec::with_capacity(left.len());
        for (_, f, _) in left.iter() {
            graphs.push(self.canonical_uf_graph(model, f, apps));
        }
        // INNERMOST: the free point takes the OTHER side's canonical value, so
        // both chains continue from the SAME point and every outer level is
        // then forced by congruence. Nothing else in the formula constrains
        // this point (free-point test above), so the choice is legal.
        let Some(mut current) = graphs[depth]
            .get(&other_key)
            .cloned()
            .or_else(|| self.model_int_value(model, other[depth].0))
        else {
            return false;
        };
        // (target_term_free, target_term_other, value, table_key_if_free_point)
        let mut plan: Vec<(TermId, TermId, BigInt, Option<(usize, BigInt)>)> = Vec::new();
        plan.push((
            free[depth].0,
            other[depth].0,
            current.clone(),
            Some((depth, free_key.clone())),
        ));
        // OUTER LEVELS: read the canonical value at the (now shared) argument
        // point. A level whose point is absent from the graph is itself free —
        // keep the value the model already committed on the OTHER side.
        for i in (0..depth).rev() {
            let next = match graphs[i].get(&current) {
                Some(v) => (v.clone(), None),
                None => {
                    let Some(v) = self
                        .model_int_value(model, other[i].0)
                        .or_else(|| self.model_int_value(model, free[i].0))
                    else {
                        return false;
                    };
                    (v, Some((i, current.clone())))
                }
            };
            plan.push((free[i].0, other[i].0, next.0.clone(), next.1));
            current = next.0;
        }
        if debug_enabled() {
            eprintln!(
                "[uflia-witness] free UF point {head}({free_key}) := {} \
                 (chain depth {}, plan {:?})",
                plan[0].2,
                left.len(),
                plan.iter().map(|p| p.2.clone()).collect::<Vec<_>>()
            );
        }
        // APPLY. Both sides are pinned to the SAME value at every level, so
        // the conjunct holds by construction and the model becomes CONGRUENT
        // along the chain (the derived applications now agree with the primary
        // domain commitments the gate reads first). Every gate still re-checks
        // the completed witness; a completion that breaks anything else
        // degrades to `unknown` exactly as the uncompleted model does today.
        let mut changed = false;
        for (free_term, other_term, value, free_row) in plan {
            for term in [free_term, other_term] {
                if self.model_int_value(model, term).as_ref() != Some(&value) {
                    changed = true;
                }
                self.pin_int_app_value(model, term, &value);
            }
            if let Some((level, key)) = free_row {
                let head_name = left[level].1.clone();
                self.add_uf_table_row(model, &head_name, free_term, &key, &value);
                changed = true;
            }
        }
        let _ = (l_app, r_app);
        changed
    }

    /// Pin an Int-sorted UF APPLICATION to a committed value in every slot the
    /// evaluators read, in their own precedence order
    /// (`func_app_const_terms` > non-speculative `term_values` > table >
    /// `int_values`), so solver-side evaluation, the independent gate's view
    /// and the model printer all observe ONE value.
    fn pin_int_app_value(&mut self, model: &mut Model, app: TermId, value: &BigInt) {
        if let TermData::App(sym, _) = self.ctx.terms.get(app) {
            if model.has_certified_total_uf(sym.name()) {
                return;
            }
        }
        let const_term = self.ctx.terms.mk_int(value.clone());
        super::eval_memo_clear();
        if let Some(euf) = model.euf_model.as_mut() {
            euf.func_app_const_terms.insert(app, const_term);
            euf.term_values.insert(app, value.to_string());
            euf.int_values.insert(app, value.clone());
            euf.speculative_int_terms.remove(&app);
        }
        if let Some(lia) = model.lia_model.as_mut() {
            lia.values.insert(app, value.clone());
        }
        model
            .completed_values
            .insert(app, EvalValue::Rational(BigRational::from(value.clone())));
    }

    /// Append a concrete `(arg_value) -> result_value` row to a function table
    /// so the PRINTED interpretation and every congruent lookup agree with the
    /// pin we just installed on the application term.
    ///
    /// `function_tables[name]` and `function_table_terms[name]` are POSITIONALLY
    /// aligned: `combiner_models` zips them to recover each row's source
    /// application, and a length mismatch marks the whole table conflicted. If
    /// they are ALREADY misaligned we therefore skip the row entirely rather
    /// than pad the vector — padding would re-attribute the pre-existing rows
    /// to the wrong source terms. Skipping costs nothing: the per-application
    /// pins in [`Self::pin_int_app_value`] are read first by every evaluator,
    /// and the table row is only the printer-visible echo of them.
    fn add_uf_table_row(
        &mut self,
        model: &mut Model,
        name: &str,
        source_app: TermId,
        arg_value: &BigInt,
        result_value: &BigInt,
    ) {
        if model.has_certified_total_uf(name) {
            return;
        }
        let Some(euf) = model.euf_model.as_mut() else {
            return;
        };
        let rows = euf.function_tables.get(name).map_or(0, Vec::len);
        let sources = euf.function_table_terms.get(name).map_or(0, Vec::len);
        if rows != sources {
            if debug_enabled() {
                eprintln!(
                    "[uflia-witness] table row for {name} SKIPPED (rows={rows} sources={sources})"
                );
            }
            return;
        }
        let table = euf.function_tables.entry(name.to_string()).or_default();
        let key = vec![arg_value.to_string()];
        if table
            .iter()
            .any(|(args, _)| args.len() == 1 && args[0] == key[0])
        {
            // A literal row for this point already exists; do not shadow it.
            return;
        }
        table.push((key, result_value.to_string()));
        euf.function_table_terms
            .entry(name.to_string())
            .or_default()
            .push(source_app);
    }

    fn pin_int_leaf_value(&mut self, model: &mut Model, leaf: TermId, value: &BigInt) {
        super::eval_memo_clear();
        if let Some(lia) = model.lia_model.as_mut() {
            lia.values.insert(leaf, value.clone());
        }
        if let Some(euf) = model.euf_model.as_mut() {
            euf.int_values.insert(leaf, value.clone());
            euf.term_values.insert(leaf, value.to_string());
            euf.speculative_int_terms.remove(&leaf);
        }
        model
            .completed_values
            .insert(leaf, EvalValue::Rational(BigRational::from(value.clone())));
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashSet;
    use ay_core::term::Symbol;
    use ay_core::{Sort, TermId};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use crate::executor::model::{EvalValue, Model};
    use crate::executor::Executor;

    /// `0 <= x` and `(< x 7)` — the shape the mathsat Hash family asserts for
    /// every index variable — must yield the half-open interval `[0, 7)`.
    fn hash_family_bounds_executor() -> (Executor, TermId, TermId) {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let y = exec.ctx.terms.mk_var("y", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let seven = exec.ctx.terms.mk_int(BigInt::from(7));
        for (sym, a, b) in [
            ("<=", zero, x),
            ("<", x, seven),
            ("<=", zero, y),
            ("<", y, seven),
        ] {
            let atom = exec
                .ctx
                .terms
                .mk_app(Symbol::named(sym), vec![a, b], Sort::Bool);
            exec.ctx.assertions.push(atom);
        }
        let eq = exec.ctx.terms.mk_eq(x, y);
        let diseq = exec.ctx.terms.mk_not(eq);
        exec.ctx.assertions.push(diseq);
        (exec, x, y)
    }

    #[test]
    fn asserted_int_ranges_reads_the_half_open_hash_family_interval() {
        let (exec, x, y) = hash_family_bounds_executor();
        let ranges = exec.asserted_int_ranges();
        for leaf in [x, y] {
            let range = ranges
                .get(&leaf)
                .expect("a leaf with both bounds asserted must be indexed");
            assert_eq!(range.lo, BigInt::from(0));
            assert_eq!(range.hi, BigInt::from(7), "`(< x 7)` is EXCLUSIVE");
        }
    }

    /// A leaf with only ONE side bounded is NOT a range-carrying leaf: the
    /// diseq shift may still move it anywhere, exactly as today.
    #[test]
    fn asserted_int_ranges_ignores_a_one_sided_bound() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let atom = exec
            .ctx
            .terms
            .mk_app(Symbol::named("<="), vec![zero, x], Sort::Bool);
        exec.ctx.assertions.push(atom);
        assert!(exec.asserted_int_ranges().is_empty());
    }

    /// `(not (= x y))` — the normalized form of a two-way `distinct` — must
    /// register BOTH directions, so the shift's free-value search sees the
    /// peer's value whichever side it is asked about.
    #[test]
    fn asserted_int_diseq_peers_are_symmetric() {
        let (exec, x, y) = hash_family_bounds_executor();
        let peers = exec.asserted_int_diseq_peers();
        assert_eq!(peers.get(&x).map(Vec::as_slice), Some(&[y][..]));
        assert_eq!(peers.get(&y).map(Vec::as_slice), Some(&[x][..]));
    }

    /// With the lever OFF the range-aware shift is byte-identical: it returns
    /// the caller's fresh sentinel unchanged even for a bound-carrying leaf.
    /// (The env gate is process-global and `OnceLock`-cached, so this asserts
    /// the DEFAULT posture the test binary runs under.)
    #[test]
    fn bounded_diseq_shift_is_inert_while_the_lever_is_off() {
        assert!(
            !super::uflia_witness_complete_enabled(),
            "the test binary must run with the lever at its default OFF"
        );
        let (exec, x, _) = hash_family_bounds_executor();
        let model = Model::empty();
        let ranges = exec.asserted_int_ranges();
        let peers = exec.asserted_int_diseq_peers();
        assert_eq!(
            exec.uflia_bounded_diseq_shift_value(&model, &ranges, &peers, x, 1_000_003),
            Some(1_000_003)
        );
    }

    #[test]
    fn flatten_or_overflow_never_returns_a_partial_allowed_set() {
        let mut exec = Executor::new();
        let p = exec.ctx.terms.mk_var("p", Sort::Bool);
        let q = exec.ctx.terms.mk_var("q", Sort::Bool);
        let disjunction = exec
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![p, q], Sort::Bool);

        assert!(
            exec.flatten_or_with_limits(disjunction, 1, 8).is_none(),
            "crossing the disjunct fence must discard the whole authority set"
        );
        assert_eq!(
            exec.flatten_or_with_limits(disjunction, 2, 8).as_deref(),
            Some(&[p, q][..])
        );
    }

    #[test]
    fn application_index_overflow_never_returns_a_partial_free_point_view() {
        let mut exec = Executor::new();
        let p = exec.ctx.terms.mk_var("p", Sort::Bool);
        let not_p = exec.ctx.terms.mk_not(p);
        exec.ctx.assertions.push(not_p);
        let unary_ufs = DetHashSet::default();

        assert!(
            exec.unary_uf_application_index_with_limit(&unary_ufs, 1)
                .is_none(),
            "crossing the DAG fence must disable free-point completion"
        );
        assert!(exec
            .unary_uf_application_index_with_limit(&unary_ufs, 2)
            .is_some());
    }

    #[test]
    fn witness_repair_cannot_mutate_a_certified_total_uf() {
        let mut exec = Executor::new();
        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let f_one = exec
            .ctx
            .terms
            .mk_app(Symbol::named("f"), vec![one], Sort::Int);
        let mut model = Model::empty();
        model
            .install_certified_total_uf(
                "f".to_string(),
                vec![Sort::Int],
                Sort::Int,
                Vec::new(),
                EvalValue::Rational(BigRational::from_integer(BigInt::from(0))),
            )
            .expect("well-typed certified total UF");
        let before = model
            .euf_model
            .as_ref()
            .expect("rendered table")
            .function_tables["f"]
            .clone();

        exec.pin_int_app_value(&mut model, f_one, &BigInt::from(7));
        exec.add_uf_table_row(&mut model, "f", f_one, &BigInt::from(1), &BigInt::from(7));

        assert_eq!(
            model
                .euf_model
                .as_ref()
                .expect("rendered table")
                .function_tables["f"],
            before,
            "post-certificate repair must not change the printed total table"
        );
        assert!(!model.completed_values.contains_key(&f_one));
        assert_eq!(
            exec.evaluate_term(&model, f_one),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(0)))
        );
    }
}
