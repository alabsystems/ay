// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF Bool-atom assignment and merge helpers.

use ay_core::term::{TermData, TermId};
use ay_core::{Sort, TheoryLit};
use tracing::debug;

use ay_core::kani_compat::DetHashMap;

use crate::solver::EufSolver;
use crate::types::{EqualityReason, MergeReason};

thread_local! {
    /// Bool-arg app pairs recorded by the most recent
    /// `bool_arg_model_is_congruent` call that DOWNGRADED a candidate `Sat` to
    /// `Unknown`.
    ///
    /// A thread-local rather than a return value because the `EufSolver` that
    /// computes them is constructed inside
    /// `solve_incremental_split_loop_pipeline!`'s `create_theory` block and never
    /// escapes it, so the executor cannot read the field off the solver. This is
    /// the bridge that lets `solve_euf` attempt a targeted congruence repair
    /// instead of surrendering the check-sat.
    ///
    /// DIAGNOSTIC ONLY — nothing inside the solver reads it, so writing it cannot
    /// change a verdict. Cleared by `take_bool_arg_repair_candidates`.
    static BOOL_ARG_REPAIR_CANDIDATES: std::cell::RefCell<Vec<(TermId, TermId)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Take (and clear) the Bool-arg app pairs recorded by the last congruence-guard
/// downgrade on this thread. Empty when the guard did not fire.
pub fn take_bool_arg_repair_candidates() -> Vec<(TermId, TermId)> {
    BOOL_ARG_REPAIR_CANDIDATES.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// Clear any stale candidates before a solve, so a later `take` cannot observe
/// pairs left over from an earlier check-sat on the same thread.
pub fn clear_bool_arg_repair_candidates() {
    BOOL_ARG_REPAIR_CANDIDATES.with(|c| c.borrow_mut().clear());
}

fn record_bool_arg_repair_candidates(edges: &[(TermId, TermId)]) {
    BOOL_ARG_REPAIR_CANDIDATES.with(|c| {
        let mut slot = c.borrow_mut();
        slot.clear();
        slot.extend_from_slice(edges);
    });
}

impl EufSolver<'_> {
    pub(crate) fn record_assignment(&mut self, term: TermId, value: bool) {
        let debug = self.debug_euf;
        match self.assigns.get(&term).copied() {
            Some(prev) if prev == value => {
                if debug {
                    safe_eprintln!(
                        "[EUF] record_assignment: term {} = {} (unchanged)",
                        term.0,
                        value
                    );
                }
            }
            Some(prev) => {
                if debug {
                    safe_eprintln!(
                        "[EUF] record_assignment: CONFLICT term {} was {} now {}",
                        term.0,
                        prev,
                        value
                    );
                }
                self.pending_conflict = Some(term);
            }
            None => {
                self.trail.push((term, None));
                self.assigns.insert(term, value);
                // #euf-ite-worklist: this assignment may unblock ITE terms whose
                // condition is (or negates) `term`. Enqueue exactly those.
                if let Some(ites) = self.ite_by_cond.get(&term.0) {
                    let ites = ites.clone();
                    self.pending_ite.extend(ites);
                }
                self.dirty = true;

                // #euf-idle-rebuild: feed the incremental bool-valued-atom
                // merge (same qualification filter as the full rescan in
                // `incremental_merge_bool_valued_atoms`, production mode).
                {
                    let is_bool = if (term.0 as usize) < self.bool_sorted.len() {
                        self.bool_sorted[term.0 as usize]
                    } else {
                        self.terms.sort(term) == &Sort::Bool
                    };
                    if is_bool {
                        let qualifies = match self.terms.get(term) {
                            TermData::Var(_, _) => true,
                            TermData::App(sym, _) => !Self::is_builtin_symbol(sym),
                            _ => false,
                        };
                        if qualifies {
                            self.bool_merge_pending.push((term.0, value));
                        }
                    }
                }

                // #euf-prop-gap: env-gated profiling — did the e-graph (stale
                // pre-batch view: queued `to_merge` entries not yet applied)
                // already entail or contradict this new assignment?
                if self.gap_stats_enabled {
                    if let Some((lhs, rhs)) = self.decode_eq(term) {
                        if self.enodes_init
                            && self.terms.sort(lhs) == self.terms.sort(rhs)
                            && (lhs.0 as usize) < self.enodes.len()
                            && (rhs.0 as usize) < self.enodes.len()
                        {
                            self.gap_stats.eq_asserts += 1;
                            if self.gap_stats.eq_asserts.is_multiple_of(1024) {
                                self.gap_stats.print(self.propagation_count);
                            }
                            let lr = self.enode_find_const(lhs.0);
                            let rr = self.enode_find_const(rhs.0);
                            if lr == rr {
                                if value {
                                    self.gap_stats.pos_redundant += 1;
                                } else {
                                    self.gap_stats.neg_conflict += 1;
                                }
                            } else {
                                let key = (lr.min(rr), lr.max(rr));
                                if let Some(&(_, _, dterm)) = self.diseq_pair_index.get(&key) {
                                    if self.assigns.get(&dterm) == Some(&false) {
                                        if value {
                                            self.gap_stats.pos_conflict += 1;
                                        } else {
                                            self.gap_stats.neg_redundant += 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                if value {
                    self.try_track_func_app_value(term);
                } else {
                    // #8471: A new negated equality (a != b) may produce new
                    // disequalities for Nelson-Oppen. Bump the merge_epoch so
                    // that collect_implied_disequalities re-scans. Without this,
                    // the epoch check sees no change and skips the scan, missing
                    // the freshly asserted disequality.
                    if let Some((a, b)) = self.decode_eq(term) {
                        self.merge_epoch = self.merge_epoch.wrapping_add(1);
                        // #8471: Track the specific negated equality for
                        // fine-grained scan filtering.
                        self.new_negated_eqs.push((term, a, b));
                        // #inc-neg: queue for the incremental disequality
                        // index; reps are resolved at the next
                        // `propagate_disequalities` call (post-rebuild).
                        if self.inc_neg_enabled {
                            self.pending_neg_eqs.push((term, a, b));
                        }
                    }
                }

                if value {
                    if let Some((lhs, rhs)) = self.decode_eq(term) {
                        if self.terms.sort(lhs) == self.terms.sort(rhs) {
                            if !self.enodes_init {
                                self.init_enodes();
                            }
                            self.ensure_enodes_size(lhs.0);
                            self.ensure_enodes_size(rhs.0);

                            let lhs_root = self.enode_find_const(lhs.0);
                            let rhs_root = self.enode_find_const(rhs.0);
                            if lhs_root != rhs_root {
                                self.to_merge.push_back(MergeReason {
                                    a: lhs.0,
                                    b: rhs.0,
                                    reason: EqualityReason::Direct(term),
                                });

                                if debug {
                                    safe_eprintln!(
                                        "[EUF] record_assignment: eq term {} (terms {} == {}) queued for merge",
                                        term.0, lhs.0, rhs.0
                                    );
                                }
                            }

                            if lhs != rhs && !self.propagated_eqs.contains(&term) {
                                self.propagated_eqs.insert(term);
                                let reason = vec![TheoryLit::new(term, true)];
                                self.queue_pending_propagation(
                                    lhs,
                                    rhs,
                                    reason,
                                    "asserted equality",
                                );
                            }
                        }
                    }
                }

                if debug && self.decode_eq(term).is_some() {
                    safe_eprintln!(
                        "[EUF] record_assignment: eq term {} = {} (NEW, dirty=true, total_assigns={})",
                        term.0,
                        value,
                        self.assigns.len()
                    );
                }
            }
        }
    }

    /// Incremental-mode variant of merge_bool_valued_atoms.
    /// Queues BoolValue merges into to_merge for incremental_propagate(). (#4610)
    ///
    /// #euf-idle-rebuild: the full O(|assigns|) scan below runs only when
    /// `egraph_requeue_needed` (after pop/reset/unwind, when applied BoolValue
    /// merges may have been undone) or under the test-only
    /// `bool_arg_congruence` mode (whose derived-wrapper pass reads the whole
    /// model). Otherwise only the assignments recorded since the last pass
    /// (`bool_merge_pending`) are folded into the persistent true/false
    /// anchors — merges only ever grow classes between requeue events, so the
    /// anchors stay valid until the next pop.
    pub(crate) fn incremental_merge_bool_valued_atoms(&mut self) -> usize {
        if !self.egraph_requeue_needed && !self.bool_arg_congruence {
            return self.incremental_merge_pending_bool_atoms();
        }
        let mut true_rep: Option<u32> = None;
        let mut false_rep: Option<u32> = None;
        let mut queued = 0usize;

        let bool_arg_congruence = self.bool_arg_congruence;
        // Reuse a persistent scratch buffer instead of allocating a fresh Vec
        // per call (this runs on every incremental propagation). Moved out via
        // `take` so the immutable `self.assigns` borrow below doesn't conflict
        // with the mutable buffer borrow; restored to `self` after the loop.
        let bool_sorted_len = self.bool_sorted.len();
        let mut bool_assigns = std::mem::take(&mut self.bool_assigns_buf);
        bool_assigns.clear();
        bool_assigns.extend(self.assigns.iter().filter_map(|(&term, &val)| {
            // Bool-sortedness is static per term id → O(1) precomputed lookup
            // (populated in init_enodes) instead of a `Sort::eq` each scan.
            // Fall back to the direct query for term ids added after the last
            // enode init (bounds-safe, behaviour-identical).
            let is_bool = if (term.0 as usize) < bool_sorted_len {
                self.bool_sorted[term.0 as usize]
            } else {
                self.terms.sort(term) == &Sort::Bool
            };
            if !is_bool {
                return None;
            }
            // #bool-arg-congruence: any Bool-sorted term that is an argument
            // to a UF application must join the true/false class so its
            // parent applications can become congruent. This covers builtin
            // (`and`/`or`/`=`/`distinct`) and connective (`not`/`xor`/`=>`/
            // `ite`) Bool args that the default Var/non-builtin-App filter
            // skips. Without it, EUF accepts non-congruent models over
            // Bool-valued UF arguments (false SAT).
            if bool_arg_congruence && self.bool_uf_arg_terms.contains(&term.0) {
                return Some((term.0, val));
            }
            match self.terms.get(term) {
                TermData::Var(_, _) => Some((term.0, val)),
                TermData::App(sym, _) if !Self::is_builtin_symbol(sym) => Some((term.0, val)),
                _ => None,
            }
        }));

        // #bool-arg-congruence: Bool UF-arg terms whose truth value is *derived*
        // rather than directly assigned. The prime case is `Not(inner)`: the SAT
        // layer assigns `inner` (assert_literal unwraps Not), so the wrapper term
        // never appears in `assigns` and the scan above misses it. Derive its
        // value from the inner atom so `(bool (not p))` apps still participate in
        // the true/false class merge.
        if bool_arg_congruence {
            for &arg in &self.bool_uf_arg_terms {
                if self.assigns.contains_key(&TermId(arg)) {
                    continue; // already collected directly above
                }
                if let Some(val) = self.derive_bool_term_value(TermId(arg)) {
                    bool_assigns.push((arg, val));
                }
            }
        }
        bool_assigns.sort_unstable();
        bool_assigns.dedup();

        for &(term_id, val) in &bool_assigns {
            let rep = if val { &mut true_rep } else { &mut false_rep };
            if let Some(existing_rep) = *rep {
                if self.enode_find_const(term_id) != self.enode_find_const(existing_rep) {
                    self.to_merge.push_back(MergeReason {
                        a: term_id,
                        b: existing_rep,
                        reason: EqualityReason::BoolValue {
                            term: TermId(term_id),
                            value: val,
                        },
                    });
                    queued += 1;
                }
            } else {
                *rep = Some(term_id);
            }
        }

        // Return the scratch buffer for reuse next call (keeps its capacity).
        self.bool_assigns_buf = bool_assigns;

        // #euf-idle-rebuild: this full rescan covers every currently-assigned
        // qualifying atom, so the pending feed is consumed and the anchors are
        // re-elected from the scan's representatives.
        self.bool_merge_pending.clear();
        self.bool_true_anchor = true_rep;
        self.bool_false_anchor = false_rep;

        if queued > 0 {
            debug!(
                target: "ay::euf",
                queued,
                "EUF Bool-value merges queued for incremental closure"
            );
        }

        queued
    }

    /// #euf-idle-rebuild: incremental arm of
    /// [`Self::incremental_merge_bool_valued_atoms`] — fold only the
    /// assignments recorded since the last pass into the persistent
    /// true/false anchors. Merges only ever grow classes between requeue
    /// events (pop/reset/unwind force the full rescan), so an atom already
    /// merged stays merged and only NEW atoms need queueing.
    fn incremental_merge_pending_bool_atoms(&mut self) -> usize {
        let mut queued = 0usize;
        if self.bool_merge_pending.is_empty() {
            return 0;
        }
        let mut pending = std::mem::take(&mut self.bool_merge_pending);
        for &(term_id, val) in &pending {
            let anchor = if val {
                self.bool_true_anchor
            } else {
                self.bool_false_anchor
            };
            match anchor {
                None => {
                    if val {
                        self.bool_true_anchor = Some(term_id);
                    } else {
                        self.bool_false_anchor = Some(term_id);
                    }
                }
                Some(existing_rep) => {
                    self.ensure_enodes_size(term_id);
                    self.ensure_enodes_size(existing_rep);
                    if self.enode_find_const(term_id) != self.enode_find_const(existing_rep) {
                        self.to_merge.push_back(MergeReason {
                            a: term_id,
                            b: existing_rep,
                            reason: EqualityReason::BoolValue {
                                term: TermId(term_id),
                                value: val,
                            },
                        });
                        queued += 1;
                    }
                }
            }
        }
        pending.clear();
        // Keep the allocation for the next batch.
        self.bool_merge_pending = pending;
        if queued > 0 {
            debug!(
                target: "ay::euf",
                queued,
                "EUF Bool-value merges queued (incremental pending feed)"
            );
        }
        queued
    }

    /// Derive the truth value of a Bool-sorted term from the current model.
    /// Returns `Some(v)` ONLY when `v` is a definite consequence of the
    /// committed model (SAT assignment + EUF equality classes); returns `None`
    /// when the value cannot be determined. (#bool-arg-congruence)
    ///
    /// This is the verdict-authority evaluator for the SOUND post-SAT Bool-arg
    /// congruence guard (`bool_arg_model_is_congruent`). The guard fires only on
    /// pairs whose Bool args it can fully determine, then downgrades a
    /// non-congruent `Sat` to `Unknown` (never UNSAT). For the guard to catch
    /// the incremental false-SATs, it must determine the truth value of Bool
    /// args that the SAT layer never branched on because they appear ONLY inside
    /// opaque UF applications (e.g. `fb(or false p1)`): such compound terms are
    /// not in `assigns`, so a bare `assigns`/`Not`/const lookup leaves them
    /// undetermined and the guard silently skips the violation.
    ///
    /// SOUNDNESS: every value returned here is entailed by the current model:
    /// - `assigns` is the SAT-committed value (authoritative).
    /// - Bool constants are structural.
    /// - connectives (`not`/`and`/`or`/`xor`/`=>`/`ite`) fold from their
    ///   operands using short-circuit rules that only conclude a value when it
    ///   is forced regardless of any undetermined operand.
    ///
    /// It does NOT recurse into UF apps or `pb(..)` predicate atoms beyond the
    /// `assigns` lookup, and does NOT read the e-graph — those are opaque unless
    /// the SAT layer assigned them. Undetermined operands collapse to `None`,
    /// leaving the `Sat` verdict intact (incompleteness, never unsoundness).
    pub(crate) fn derive_bool_term_value(&self, term: TermId) -> Option<bool> {
        if let Some(&v) = self.assigns.get(&term) {
            return Some(v);
        }
        match self.terms.get(term) {
            TermData::Not(inner) => self.derive_bool_term_value(*inner).map(|v| !v),
            TermData::Const(ay_core::term::Constant::Bool(b)) => Some(*b),
            TermData::Ite(c, t, e) => match self.derive_bool_term_value(*c) {
                Some(true) => self.derive_bool_term_value(*t),
                Some(false) => self.derive_bool_term_value(*e),
                None => {
                    // Condition undetermined: still definite if both branches
                    // agree on a determined value.
                    let tv = self.derive_bool_term_value(*t)?;
                    let ev = self.derive_bool_term_value(*e)?;
                    (tv == ev).then_some(tv)
                }
            },
            TermData::App(sym, args) => self.derive_bool_app_value(sym.name(), args),
            _ => None,
        }
    }

    /// Fold a Boolean connective application to a definite value from its
    /// operands. Helper for `derive_bool_term_value`; see its soundness
    /// contract. Only short-circuit conclusions (forced regardless of any
    /// undetermined operand) are returned; anything else is `None`.
    fn derive_bool_app_value(&self, name: &str, args: &[TermId]) -> Option<bool> {
        match name {
            "and" => {
                // false if ANY operand is false; true only if ALL are true.
                let mut all_true = true;
                for &a in args {
                    match self.derive_bool_term_value(a) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all_true = false,
                    }
                }
                all_true.then_some(true)
            }
            "or" => {
                // true if ANY operand is true; false only if ALL are false.
                let mut all_false = true;
                for &a in args {
                    match self.derive_bool_term_value(a) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => all_false = false,
                    }
                }
                all_false.then_some(false)
            }
            "xor" => {
                // Definite only if every operand is determined.
                let mut acc = false;
                for &a in args {
                    acc ^= self.derive_bool_term_value(a)?;
                }
                Some(acc)
            }
            "=>" => {
                // SMT-LIB `=>` is right-associative: (=> a b c) = (=> a (=> b c)).
                // Equivalent to (or (not a_1) .. (not a_{n-1}) a_n). True if any
                // antecedent is false or the consequent is true; false only if
                // every antecedent is true and the consequent is false.
                if args.is_empty() {
                    return None;
                }
                let (consequent, antecedents) = args.split_last().unwrap();
                let mut all_ante_true = true;
                for &a in antecedents {
                    match self.derive_bool_term_value(a) {
                        Some(false) => return Some(true),
                        Some(true) => {}
                        None => all_ante_true = false,
                    }
                }
                match self.derive_bool_term_value(*consequent) {
                    Some(true) => Some(true),
                    Some(false) if all_ante_true => Some(false),
                    _ => None,
                }
            }
            // Bool-sorted `=`/`distinct` over determinable Bool operands.
            "=" if args.len() >= 2 && self.terms.sort(args[0]) == &Sort::Bool => {
                let mut vals: Vec<bool> = Vec::with_capacity(args.len());
                for &a in args {
                    vals.push(self.derive_bool_term_value(a)?);
                }
                Some(vals.windows(2).all(|w| w[0] == w[1]))
            }
            "distinct" if args.len() >= 2 && self.terms.sort(args[0]) == &Sort::Bool => {
                let mut vals: Vec<bool> = Vec::with_capacity(args.len());
                for &a in args {
                    vals.push(self.derive_bool_term_value(a)?);
                }
                // Over Bool there are only two values, so >2 args can never be
                // pairwise distinct; for 2 args it is the inequality.
                if vals.len() == 2 {
                    Some(vals[0] != vals[1])
                } else {
                    Some(false)
                }
            }
            _ => None,
        }
    }

    /// Read-only SOUND check that the current model is congruent over Bool
    /// UF-arguments. Returns `false` iff it finds two UF applications that are
    /// identical in every non-Bool argument position and whose differing Bool
    /// args all share the same *model* truth value (so the applications MUST be
    /// equal by congruence), yet are in DIFFERENT equivalence classes. In that
    /// case the candidate SAT model is non-congruent and the caller must
    /// downgrade `Sat` to `Unknown`. (#bool-arg-congruence)
    ///
    /// This is the SOUND fallback for the Bool-arg congruence gap: unlike the
    /// truth-value class MERGE (which can emit unfaithful conflicts and produce
    /// a false UNSAT), this never asserts UNSAT — it only ever refuses to
    /// certify a model whose Bool-arg congruence it cannot confirm. It catches
    /// the `uf_fs2`-class false-SAT (syntactically-distinct-but-model-equal
    /// complex Bool args nested under UFs) without any false-UNSAT risk.
    ///
    /// Truth values are taken ONLY from committed assignments / `Not` / Bool
    /// constants via `derive_bool_term_value` (all sound). A pair whose Bool
    /// args' values cannot all be determined is conservatively SKIPPED (leaves
    /// the `Sat` verdict intact — incompleteness, never unsoundness).
    ///
    /// CRUCIAL completeness refinement: it fires ONLY when the two forced-equal
    /// apps are ALSO forced APART by an asserted disequality / `distinct` (their
    /// representatives are a "separated" pair). Two same-signature apps merely
    /// sitting in different e-classes is NOT a non-congruent model when nothing
    /// forces them unequal — the model is perfectly satisfiable (they just
    /// happen not to have been merged). Without this, the guard downgrades vast
    /// numbers of legitimate SAT models (CLEARSY completeness collapse). With
    /// it, the guard fires exactly on genuine congruence violations (the model
    /// would be UNSAT if congruence were enforced), so downgrading to Unknown is
    /// both sound and completeness-preserving.
    pub(crate) fn bool_arg_model_is_congruent(&mut self) -> bool {
        use hashbrown::hash_map::Entry;
        // Skip in verification-only solvers: they only re-check Unsat verdicts
        // (reasons discarded) and must not downgrade to Unknown. Also skip when
        // the validation flag is off or there are no Bool UF-args.
        if self.verify_only || !self.bool_arg_validate || self.bool_uf_arg_terms.is_empty() {
            return true;
        }
        if !self.func_apps_init {
            self.init_func_apps();
        }
        if !self.enodes_init {
            return true;
        }

        let nverts = self.enodes.len() as u32;
        // Scratch union-find over current e-class representatives. `find`/`union`
        // operate on the *current* model's classes (seeded by enode_find_const),
        // so the closure below only adds the Bool-arg congruence merges on top of
        // what EUF already derived.
        let mut parent: Vec<u32> = (0..nverts).collect();
        fn sfind(parent: &mut [u32], mut x: u32) -> u32 {
            while parent[x as usize] != x {
                parent[x as usize] = parent[parent[x as usize] as usize];
                x = parent[x as usize];
            }
            x
        }
        // Seed with current EUF classes.
        for v in 0..nverts {
            let r = self.enode_find_const(v);
            let rr = sfind(&mut parent, r);
            let vr = sfind(&mut parent, v);
            if vr != rr {
                parent[vr as usize] = rr;
            }
        }

        // Collect the forced-equal Bool-arg app pairs: two UF apps with the same
        // (func_hash, non-Bool-arg current-reps, Bool-arg model truth values)
        // MUST be congruent. Record them as union edges.
        // #euf-guard-hash: this ran on `std::collections::HashMap`, i.e. SipHash-1-3
        // with no reserved capacity, on the hottest path in the division AY is
        // losing. Profiled on CLEARSY 0002/00126: this whole function is 28.3% of
        // the solve, `hashbrown::rustc_entry` under it 15.8%, and pure table
        // growth (`reserve_rehash`) 9.7% — with `sip::Hasher::write` the single
        // largest self-time frame in the process at 11.8%.
        // `DetHashMap` is hashbrown + foldhash FixedState: faster AND
        // deterministic (the crate-wide convention, see kani_compat). Capacity is
        // known up front — one app per func_app at most.
        let mut sig_to_app: DetHashMap<(u64, Vec<u32>, Vec<bool>), u32> =
            DetHashMap::with_capacity_and_hasher(self.bool_arg_app_idx.len(), Default::default());
        let mut forced_edges: Vec<(u32, u32)> = Vec::new();
        // #euf-guard-index: iterate ONLY the apps that have a Bool argument.
        // This used to walk every func_app and `continue` on the ones with none,
        // paying a `args.clone()` heap allocation apiece to find that out. Which
        // apps qualify is fixed by argument sorts, so it is precomputed once in
        // `init_func_apps`. `has_bool` is now an invariant of the index rather
        // than something rediscovered per check.
        //
        // The clone is gone too: `derive_bool_term_value` and `TermStore::sort`
        // both take `&self`, and the only mutable borrow in the loop is the local
        // `parent` union-find, so the arguments can be read in place.
        for idx in 0..self.bool_arg_app_idx.len() {
            let app = &self.func_apps[self.bool_arg_app_idx[idx] as usize];
            let app_term = app.term_id;
            let func_hash = app.func_hash;
            let mut non_bool_reps: Vec<u32> = Vec::new();
            let mut bool_vals: Vec<bool> = Vec::new();
            let mut undetermined = false;
            for &arg in &app.args {
                if self.terms.sort(TermId(arg)) == &Sort::Bool {
                    match self.derive_bool_term_value(TermId(arg)) {
                        Some(v) => bool_vals.push(v),
                        None => {
                            undetermined = true;
                            break;
                        }
                    }
                } else {
                    non_bool_reps.push(sfind(&mut parent, arg));
                }
            }
            if undetermined {
                continue;
            }
            match sig_to_app.entry((func_hash, non_bool_reps, bool_vals)) {
                Entry::Vacant(e) => {
                    e.insert(app_term);
                }
                Entry::Occupied(e) => {
                    forced_edges.push((*e.get(), app_term));
                }
            }
        }
        // Record the forced pairs for a caller that wants to REPAIR rather than
        // give up (targeted CEGAR — see `last_bool_arg_forced_edges`). Diagnostic
        // only; no solver path reads it, so this cannot change a verdict.
        self.last_bool_arg_forced_edges = forced_edges
            .iter()
            .map(|&(a, b)| (TermId(a), TermId(b)))
            .collect();
        // Also publish on the thread-local bridge: the solver itself never
        // escapes the pipeline macro, so this is how `solve_euf` sees them.
        // Written whenever the guard runs (not only on downgrade) — the executor
        // reads them only when the verdict is `Unknown`, and clears before each
        // solve, so a `Sat` run leaving candidates behind is harmless.
        record_bool_arg_repair_candidates(&self.last_bool_arg_forced_edges);
        if forced_edges.is_empty() {
            return true;
        }
        // Snapshot the BASELINE classes (live e-graph seed only, BEFORE any
        // forced Bool-arg edge). A violation is attributable to the Bool-arg
        // congruence gap ONLY if it relates terms that the base solver kept in
        // DIFFERENT classes; two terms already merged in the baseline cannot
        // carry a Bool-arg-induced contradiction (the base solver already
        // checked them). Comparing baseline-vs-closed reps prevents the guard
        // from over-firing on dense models where the broad congruence-closure
        // fixpoint coincidentally collapses classes that were already distinct-
        // and-consistent in the accepted model (the CLEARSY completeness cost).
        let baseline: Vec<u32> = {
            let mut b = parent.clone();
            for v in 0..nverts {
                sfind(&mut b, v);
            }
            b
        };
        let base_rep = |b: &[u32], mut x: u32| -> u32 {
            while b[x as usize] != x {
                x = b[x as usize];
            }
            x
        };
        // Apply the forced Bool-arg congruence edges, then (transitively) close
        // ordinary congruence over ALL func_apps so nested wrappers like
        // `f(fb(A))` / `f(fb(B))` also collapse. A bounded fixpoint.
        for (a, b) in &forced_edges {
            let ra = sfind(&mut parent, *a);
            let rb = sfind(&mut parent, *b);
            if ra != rb {
                parent[ra as usize] = rb;
            }
        }
        if self.bool_arg_validate_transitive {
            // Congruence-closure fixpoint over func_apps: equal func + equal arg
            // reps => merge the apps. Bounded by func_apps count per round.
            let mut changed = true;
            let mut rounds = 0usize;
            let max_rounds = self.func_apps.len() + 2;
            // #euf-guard-hash: allocated ONCE and cleared per round. It used to be
            // a fresh SipHash map per round, with up to `func_apps.len()+2`
            // rounds — a Theta(n^2) allocation pattern on the hot path.
            // #euf-guard-scratch: the map and the per-app key `Vec`s are
            // solver-owned scratch, taken/restored per call (the
            // `scratch_cong_neg_la` idiom). The guard runs once per complete
            // candidate model — ~16k times on the heaviest Inc QF_Equality file —
            // and each call otherwise builds a fresh map plus one `Vec<u32>` per
            // func_app per round. Between rounds the keys are reclaimed by
            // `drain()` into the pool rather than dropped by `clear()`, so steady
            // state allocates nothing. (Keys consumed on the Occupied arm are
            // lost to the pool; that arm fires only when two apps collide on a
            // signature, i.e. exactly when a merge happens, which is rare.)
            let mut cong = std::mem::take(&mut self.scratch_bool_arg_cong);
            let mut pool = std::mem::take(&mut self.scratch_bool_arg_pool);
            cong.reserve(self.func_apps.len().saturating_sub(cong.capacity()));
            while changed && rounds < max_rounds {
                changed = false;
                rounds += 1;
                for ((_, k), _) in cong.drain() {
                    pool.push(k);
                }
                for i in 0..self.func_apps.len() {
                    let app_term = self.func_apps[i].term_id;
                    let func_hash = self.func_apps[i].func_hash;
                    let mut arg_reps = pool.pop().unwrap_or_default();
                    arg_reps.clear();
                    arg_reps.extend(
                        self.func_apps[i]
                            .args
                            .iter()
                            .map(|&a| sfind(&mut parent, a)),
                    );
                    match cong.entry((func_hash, arg_reps)) {
                        Entry::Vacant(e) => {
                            e.insert(app_term);
                        }
                        Entry::Occupied(e) => {
                            let ra = sfind(&mut parent, *e.get());
                            let rb = sfind(&mut parent, app_term);
                            if ra != rb {
                                parent[ra as usize] = rb;
                                changed = true;
                            }
                        }
                    }
                }
            }
            for ((_, k), _) in cong.drain() {
                pool.push(k);
            }
            self.scratch_bool_arg_cong = cong;
            self.scratch_bool_arg_pool = pool;
        }

        // Bool-VALUE collision: if the congruence closure merged two Bool-sorted
        // terms whose committed model truth values DISAGREE, the model is
        // non-congruent. This catches the backward direction of Bool-arg
        // congruence (the `uf_inc_1560` witness): `fb(p1)` and `fb(false)` get
        // force-merged when `p1` is modelled false, but the predicate apps over
        // them — `pb(fb p1)` (true) and `pb(fb false)` (false) — then close into
        // one class with opposing truth values. No `=`/`distinct` atom over the
        // raw `fb` terms is asserted, so the disequality scans below miss it;
        // this truth-value check is what makes the guard fire there. SOUND: it
        // only ever downgrades Sat -> Unknown when two determined-and-opposite
        // Bool values are forced together by congruence.
        {
            // Map each CLOSED class representative to the (baseline-rep, value)
            // witnesses seen for Bool terms that have a committed value. Report a
            // collision only when two witnesses share a closed class but came
            // from DIFFERENT baseline classes and disagree on value — i.e. the
            // Bool-arg congruence merge (not the base solver's own model) forced
            // two opposite-valued terms together. The baseline gate is what
            // prevents over-firing on dense models whose broad congruence-closure
            // fixpoint coincidentally collapses already-consistent classes.
            let mut class_witnesses: DetHashMap<u32, Vec<(u32, bool)>> =
                DetHashMap::with_capacity_and_hasher(self.assigns.len(), Default::default());
            for (&t, &v) in &self.assigns {
                if t.0 >= nverts || self.terms.sort(t) != &Sort::Bool {
                    continue;
                }
                let closed = sfind(&mut parent, t.0);
                let base = base_rep(&baseline, t.0);
                let seen = class_witnesses.entry(closed).or_default();
                if seen.iter().any(|&(ob, ov)| ob != base && ov != v) {
                    return false;
                }
                if !seen.iter().any(|&(ob, ov)| ob == base && ov == v) {
                    seen.push((base, v));
                }
            }
        }

        // Now check whether any asserted disequality / distinct is violated in
        // the closed scratch union-find. If so, the model is genuinely
        // non-congruent (it would be UNSAT under full Bool-arg congruence) and
        // we must NOT certify SAT.
        let neg_eqs: Vec<(TermId, TermId)> = self
            .assigns
            .iter()
            .filter(|(_, &v)| !v)
            .filter_map(|(&t, _)| self.decode_eq(t))
            .collect();
        for (lhs, rhs) in neg_eqs {
            if self.terms.sort(lhs) == self.terms.sort(rhs)
                && lhs.0 < nverts
                && rhs.0 < nverts
                && sfind(&mut parent, lhs.0) == sfind(&mut parent, rhs.0)
            {
                return false;
            }
        }
        let distinct_terms: Vec<Vec<TermId>> = self
            .assigns
            .iter()
            .filter(|(_, &v)| v)
            .filter_map(|(&t, _)| self.decode_distinct(t).map(|a| a.to_vec()))
            .collect();
        for args in &distinct_terms {
            for i in 0..args.len() {
                if args[i].0 >= nverts {
                    continue;
                }
                let ri = sfind(&mut parent, args[i].0);
                for arg in &args[i + 1..] {
                    if arg.0 >= nverts {
                        continue;
                    }
                    if ri == sfind(&mut parent, arg.0) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Build the reason literal for a `BoolValue` merge endpoint, unwrapping
    /// `Not` so the literal references the atom the SAT layer actually owns a
    /// variable for. `Not(inner) = value` is the identity `inner = !value`, so
    /// this is reason-preserving while keeping conflict clauses mappable
    /// (avoiding partial-clause SAT/UNSAT escalation). (#bool-arg-congruence)
    ///
    /// Returns `None` for a Bool CONSTANT endpoint: a constant's truth value is
    /// unconditional, so it contributes no literal to a conflict clause (and the
    /// SAT solver owns no variable for it, which would otherwise make the clause
    /// unmappable). Callers skip `None` reasons.
    pub(crate) fn bool_value_reason_lit(&self, term: TermId, value: bool) -> Option<TheoryLit> {
        match self.terms.get(term) {
            TermData::Const(ay_core::term::Constant::Bool(_)) => None,
            TermData::Not(inner) => {
                // Recurse so `not <const>` also drops out.
                match self.terms.get(*inner) {
                    TermData::Const(ay_core::term::Constant::Bool(_)) => None,
                    _ => Some(TheoryLit::new(*inner, !value)),
                }
            }
            _ => Some(TheoryLit::new(term, value)),
        }
    }
}
