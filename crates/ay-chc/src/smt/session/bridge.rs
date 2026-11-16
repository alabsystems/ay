// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheoryBridge` — the lean `ay_sat::Extension` adapter (design §2.4; contract
//! C2; owner WP-2 / B).
//!
//! Borrowed for the duration of ONE ay-sat solve (and dropped before model
//! extraction ends the query). WP-1 constructs it from `BridgeParts`, drives one
//! `solve_with_extension_and_assumptions_core` per (re-)entry, then reads
//! `exit()`, `take_originals()`, `stats()`, and pops the theory to scope 0
//! through `BridgeGuard` (`backtrack(0)`).
//!
//! Rules this file owns (all from §2.4, each cited there):
//! - per-literal theory-scope alignment with the PRE-feed cursor per pushed
//!   scope (ay-dpll `extension/propagate/trail.rs`), so a backjump into the
//!   assumption prefix re-feeds only the popped suffix and the theory sees
//!   every literal below the backjump exactly once (`feed_trail`); the theory
//!   is FLUSHED (`check_during_propagate`) before each new scope is opened,
//!   because LRA trails an atom's bounds in the scope current at its next
//!   check, not at its assertion (`feed_trail` doc);
//! - the don't-care filter: only `active_atom` vars are fed; a MINTED atom
//!   inherits the activity of the guard atom it was minted for (or is always
//!   active when it has no guard), because the session rebuilds `active_atom`
//!   from the ASSERTIONS' atoms before every query (`refresh_minted_activity`);
//! - EAGER reasons only (`propagations`, never `lazy_propagations`): LRA emits
//!   lazy `reason_data` propagations unconditionally, so the bridge
//!   materialises each one through `explain_propagation` at drain time; a
//!   propagation with an unexplainable, unmapped or non-falsified reason, or
//!   an unmapped target, is DROPPED (never lazy, never partial);
//! - the fail-closed literal mapping (`lit_of` -> `None` => `TheoryIncomplete`);
//!   an EMPTY theory conflict is `Poison(EmptyTheoryConflict)`, never returned
//!   to ay-sat (design F6 would turn it into a core-less UNSAT); a conflict
//!   literal that is not currently TRUE on the SAT trail is `TheoryIncomplete`
//!   (its negation would not be a falsified clause and the loop could livelock);
//! - `init()` does NO theory reset (called once per solve, F5); it pops the
//!   theory to scope 0 when a re-entered solve (§4.2) finds it deeper — the
//!   incremental reset drops the SAT trail above level 0 without an
//!   `ext.backtrack`;
//! - the restart-for-originals protocol: tier-2 clauses are buffered in
//!   `MintState::originals`, `check()` returns `Unknown` with
//!   `exit = RestartWithOriginals`, and the session re-enters (§4.2).
//!
//! One deliberate deviation from the §2.4 pseudo-code, recorded in the WP-2
//! status report: a `TheoryResult::Unknown` from the BCP-time
//! `check_during_propagate` does NOT end the solve. That check is
//! "sound-but-weaker" by contract (`theory/mod.rs`), its `Unknown` is not a
//! verdict, and the in-tree eager extension treats it as a label and continues
//! (`ay-dpll/src/extension/propagate/check_result.rs`). The FINAL `check()`
//! is authoritative: its `Unknown` is `Budget(Deadline)` at a deadline and
//! `TheoryIncomplete` otherwise, exactly as designed.

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ay_core::{FarkasAnnotation, TermId, TermStore, TheoryLit, TheoryResult, TseitinState};
use ay_sat::{ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext, Variable};

use super::ledger::{FarkasLedger, LedgerKind};
use super::minting::{MintOutcome, MintState, Minter, MINT_ALWAYS_ACTIVE, MINT_NONE};
use super::theory_box::TheoryBox;
use super::{Assertion, BudgetKind, ModelView, PoisonKind, SessionConfig, UnsupportedKind};
use crate::smt::types::SmtValue;
use crate::smt::SmtContext;

/// The same request answered this many times with an unchanged SAT state is a
/// theory-side bug, not a legitimate re-request (§4.1 tripwire).
const REQUEST_REPEAT_TRIP: u32 = 3;

/// State that PERSISTS across solves (lives in `HornSmt`; the bridge borrows
/// it). Keeping the dense tables here removes the per-query O(#atoms) rebuild.
#[derive(Debug, Default)]
pub(crate) struct BridgeState {
    /// Dense SAT-var -> theory atom (`None` for Tseitin / activation vars);
    /// grown at assert and on mint.
    pub(crate) atom_of_var: Vec<Option<TermId>>,
    /// Dense flag: the atom var belongs to >= 1 LIVE + ACTIVE assertion this
    /// query (don't-care filter). Rebuilt from `atom_live_refs` ∩ active set by
    /// the session before each solve: O(active atoms). Minted atoms are added
    /// by the bridge (`refresh_minted_activity`).
    pub(crate) active_atom: Vec<bool>,
    /// Level-0 trail literals already fed at theory scope 0 (permanent facts;
    /// never re-fed). MUST be cleared if the theory is ever reset
    /// (`on_theory_reset`).
    pub(crate) l0_fed: Vec<bool>,
    /// Preferred phases for minted equality atoms (`suggest_phase` table).
    pub(crate) preferred_phase: FxHashMap<u32, bool>,
    /// Atom registered with the theory (dedup).
    pub(crate) registered: Vec<bool>,
    /// Activity parent of a MINTED theory-atom var (dense, `MINT_NONE` for
    /// every var the bridge did not mint): `MINT_ALWAYS_ACTIVE`, or the index
    /// of the guard atom var whose activity the minted atom inherits (a split
    /// atom follows its disequality guard; a triangle-axiom atom follows its
    /// equality). Grown by the bridge only.
    pub(crate) mint_parent: Vec<u32>,
    /// Minted theory-atom vars in creation order (a parent always precedes
    /// its children), so one forward pass resolves activity.
    pub(crate) minted_vars: Vec<u32>,
    /// Generation of the theory scope INSTANCE an atom var was last fed in
    /// (0 = never). A scope instance gets a fresh generation at every
    /// `theory.push()`, so after a pop and re-push of the same scope number
    /// the old entries no longer match and the atom is fed again; within one
    /// instance a re-scan (a trail rewind after a backjump) skips it.
    pub(crate) fed_gen: Vec<u32>,
    /// Source of scope-instance generations (never repeats within a session).
    pub(crate) gen_counter: u32,
    /// Atom vars activated mid-solve (by the minter) whose literal was already
    /// assigned: fed at the current scope by the next `feed_trail` (see
    /// `TheoryBridge::sticky`). Cleared at `init`.
    pub(crate) late_activated: Vec<u32>,
}

impl BridgeState {
    /// Grow every dense table to cover `num_vars` variables (never shrinks).
    pub(crate) fn grow(&mut self, num_vars: usize) {
        if self.atom_of_var.len() < num_vars {
            self.atom_of_var.resize(num_vars, None);
        }
        if self.active_atom.len() < num_vars {
            self.active_atom.resize(num_vars, false);
        }
        if self.l0_fed.len() < num_vars {
            self.l0_fed.resize(num_vars, false);
        }
        if self.registered.len() < num_vars {
            self.registered.resize(num_vars, false);
        }
        if self.mint_parent.len() < num_vars {
            self.mint_parent.resize(num_vars, MINT_NONE);
        }
        if self.fed_gen.len() < num_vars {
            self.fed_gen.resize(num_vars, 0);
        }
    }

    /// The theory forgot every assertion (a defensive `soft_reset`, §2.3): the
    /// level-0 facts fed at scope 0 must be fed again, and every registration
    /// redone by the caller.
    /// The theory's ASSIGNMENT was reset (`TheorySolver::soft_reset`: bounds
    /// and values gone, atom registrations kept — `LraSolver::soft_reset_inner`
    /// preserves `registered_atoms`): the level-0 facts must be fed again, the
    /// registrations stand.
    pub(crate) fn on_theory_assignment_reset(&mut self) {
        self.l0_fed.iter_mut().for_each(|f| *f = false);
    }

    pub(crate) fn on_theory_reset(&mut self) {
        self.l0_fed.iter_mut().for_each(|f| *f = false);
        self.registered.iter_mut().for_each(|f| *f = false);
    }

    /// Re-derive the activity of every minted atom from its parent, keeping
    /// whatever the session's assertion pass already set (a minted atom can
    /// later also be an assertion atom).
    pub(crate) fn refresh_minted_activity(&mut self) {
        let n = self.active_atom.len();
        for i in 0..self.minted_vars.len() {
            let v = self.minted_vars[i] as usize;
            if v >= n {
                continue;
            }
            let p = self.mint_parent.get(v).copied().unwrap_or(MINT_NONE);
            let active = p == MINT_ALWAYS_ACTIVE
                || (p != MINT_NONE && (p as usize) < n && self.active_atom[p as usize]);
            if active {
                self.active_atom[v] = true;
            }
        }
    }

    /// Whether the atom var `v` is fed this query.
    #[inline]
    pub(crate) fn is_active(&self, v: usize) -> bool {
        self.active_atom.get(v).copied().unwrap_or(false)
    }
}

/// Why the bridge ended a solve (read by the session after
/// `ExtensionUnknown` / `TheoryStop`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BridgeExit {
    None,
    /// Non-re-derivable clauses are buffered in `MintState::originals`; the
    /// session must add them with `add_clause_global` and re-enter the solve (§4.2).
    RestartWithOriginals,
    Budget(BudgetKind),
    TheoryIncomplete,
    Unsupported(UnsupportedKind),
    Poison(PoisonKind),
}

/// Per-solve bridge counters (WP-2 extends freely; read by the session into
/// `SessionStats`). Cumulative over the bridge's life (one query, all its
/// re-entries).
#[derive(Debug, Clone, Default)]
pub(crate) struct BridgeStats {
    pub(crate) solves: u64,
    pub(crate) propagate_calls: u64,
    pub(crate) check_calls: u64,
    pub(crate) fed_literals: u64,
    /// Atom literals met again by a post-backjump rewind, already fed in the
    /// current scope instance (skipped).
    pub(crate) rescanned_fed: u64,
    /// Atoms activated mid-solve while already assigned (fed late, kept fed).
    pub(crate) late_activations: u64,
    /// Late feeds, including the re-feeds after a backjump popped their scope.
    pub(crate) late_feeds: u64,
    /// Level-0 facts fed at theory scope 0 (each at most once per session).
    pub(crate) l0_feeds: u64,
    /// A trail literal below the current theory scope (an out-of-order trail;
    /// impossible with chronological backtracking off, counted defensively).
    pub(crate) out_of_order_feeds: u64,
    pub(crate) theory_pushes: u64,
    pub(crate) theory_pops: u64,
    pub(crate) conflicts: u64,
    pub(crate) bcp_conflicts: u64,
    /// A conflict literal the encoder cannot name (fail closed -> `TheoryIncomplete`).
    pub(crate) unmapped_conflicts: u64,
    /// A conflict literal that is not TRUE on the SAT trail (fail closed).
    pub(crate) non_falsified_conflicts: u64,
    /// `check_during_propagate` answered `Unknown` (continued; the final check judges).
    pub(crate) bcp_unknowns: u64,
    pub(crate) propagations: u64,
    pub(crate) dropped_propagations: u64,
    /// Propagations whose target was already assigned false: returned as conflicts.
    pub(crate) propagation_conflicts: u64,
    pub(crate) deadline_stops: u64,
    /// `AddClauses` batches returned to ay-sat (tier 1).
    pub(crate) inline_batches: u64,
    pub(crate) inline_clauses: u64,
    /// Solves ended with `RestartWithOriginals` (tier 2).
    pub(crate) originals_restarts: u64,
    pub(crate) originals_clauses: u64,
    pub(crate) mints_diseq: u64,
    pub(crate) mints_expr: u64,
    pub(crate) mints_model_eq: u64,
    pub(crate) mints_lemma: u64,
    /// Fresh SAT variables minted for theory atoms.
    pub(crate) minted_atoms: u64,
    /// Hint rounds that minted nothing new (converged to `Sat`, §4.3).
    pub(crate) hint_convergences: u64,
    /// Model-equality rounds that minted nothing new and were re-checked
    /// without LRA's `assume_eqs`-over-split preference (Rung-4 om1relays
    /// finding; see `TheoryBridge::answer_model_eqs`).
    pub(crate) hint_rechecks: u64,
    /// The §4.1 tripwire fired (same request, unchanged assignment, thrice).
    pub(crate) tripwire_trips: u64,
    /// `init()` found the theory above scope 0 (a re-entered solve) and
    /// popped it down.
    pub(crate) init_pops: u64,
    /// Scope flushes: `check_during_propagate` calls issued by `feed_trail`
    /// before opening a new theory scope (see `feed_trail`).
    pub(crate) scope_flushes: u64,
    /// Conflicts a scope flush reported (a genuine conflict among literals at
    /// or below that scope, all on the SAT trail; returned like any other).
    pub(crate) scope_flush_conflicts: u64,
}

/// Contract C2: everything a bridge borrows for one solve.
pub(crate) struct BridgeParts<'s> {
    pub(crate) theory: &'s mut TheoryBox,
    /// For minting terms; `theory.rebind(own)` after every mutation.
    pub(crate) own: &'s mut SmtContext,
    pub(crate) tseitin: &'s mut Option<TseitinState>,
    pub(crate) st: &'s mut BridgeState,
    pub(crate) ledger: &'s mut FarkasLedger,
    /// The query number (ledger epoch).
    pub(crate) epoch: u64,
    pub(crate) cfg: &'s SessionConfig,
    pub(crate) deadline: Option<Instant>,
    pub(crate) should_stop: &'s dyn Fn() -> bool,
    pub(crate) phase_seed: Option<&'s FxHashMap<String, SmtValue>>,
}

pub(crate) struct TheoryBridge<'s> {
    theory: &'s mut TheoryBox,
    own: &'s mut SmtContext,
    tseitin: &'s mut Option<TseitinState>,
    st: &'s mut BridgeState,
    ledger: &'s mut FarkasLedger,
    cfg: &'s SessionConfig,
    epoch: u64,
    mint: MintState,
    // theory scope <-> SAT level bookkeeping (per-literal alignment, see `feed_trail`)
    theory_level: u32,
    /// `level_cursor[i - 1]` = trail position at which theory scope `i` was
    /// pushed (the PRE-feed cursor, design F20): the index of the first trail
    /// literal fed at a scope `>= i`. `backtrack(k)` restores
    /// `last_trail_pos = level_cursor[k]` so only the popped suffix is re-fed.
    level_cursor: Vec<usize>,
    /// Generation of each open scope instance (parallel to `level_cursor`).
    scope_gen: Vec<u32>,
    /// Late-fed atom literals `(var, theory scope fed at)`: a literal whose
    /// trail position is behind the cursor is fed OUT OF ORDER at the current
    /// scope; a backjump that pops that scope while SAT keeps the literal
    /// (its level is at or below the new level) re-queues it, so the theory
    /// holds it exactly as long as the SAT trail does.
    sticky: Vec<(u32, u32)>,
    last_trail_pos: usize,
    /// Lowest SAT level a `backtrack` returned to since the last feed: the
    /// solver truncated its trail to the end of that level, so every trail
    /// position the cursor had passed above it is stale (WP-4 integration
    /// finding, see `feed_trail`).
    trail_truncated_level: Option<u32>,
    deadline: Option<Instant>,
    should_stop: &'s dyn Fn() -> bool,
    exit: BridgeExit,
    stats: BridgeStats,
    /// §4.1 tripwire: the last inline batch (its clauses) with the SAT state
    /// it was answered in, and how many times in a row it recurred unchanged.
    last_request: Option<(Vec<Vec<Literal>>, usize, u64)>,
    repeat_count: u32,
    /// A conflict a scope flush reported inside `feed_trail`, delivered by
    /// the caller in place of its own theory check.
    pending_conflict: Option<(Vec<TheoryLit>, Option<FarkasAnnotation>)>,
}

impl<'s> TheoryBridge<'s> {
    pub(crate) fn new(parts: BridgeParts<'s>) -> Self {
        let BridgeParts {
            theory,
            own,
            tseitin,
            st,
            ledger,
            epoch,
            cfg,
            deadline,
            should_stop,
            phase_seed,
        } = parts;
        // The store may have been mutated by the session since the last
        // theory call (assert_persistent rebinds too, but the discipline is
        // cheap and the bridge is the one that reads through the pointer).
        theory.rebind(own);
        Self {
            theory,
            own,
            tseitin,
            st,
            ledger,
            cfg,
            epoch,
            mint: MintState::new(phase_seed.cloned()),
            theory_level: 0,
            level_cursor: Vec::new(),
            scope_gen: Vec::new(),
            sticky: Vec::new(),
            last_trail_pos: 0,
            trail_truncated_level: None,
            deadline,
            should_stop,
            exit: BridgeExit::None,
            stats: BridgeStats::default(),
            last_request: None,
            repeat_count: 0,
            pending_conflict: None,
        }
    }

    pub(crate) fn exit(&self) -> BridgeExit {
        self.exit
    }

    /// Tier-2 clauses buffered by the last solve (§4.2); empties the buffer.
    pub(crate) fn take_originals(&mut self) -> Vec<Vec<Literal>> {
        std::mem::take(&mut self.mint.originals)
    }

    pub(crate) fn stats(&self) -> &BridgeStats {
        &self.stats
    }

    /// Current theory scope depth (0 between queries).
    pub(crate) fn theory_level(&self) -> u32 {
        self.theory_level
    }

    /// Mints (all kinds) this query.
    pub(crate) fn mint_count(&self) -> u32 {
        self.mint.count
    }

    /// Lend the parts `model::extract` reads while the theory is still at the
    /// final scope (between the solve and the guard's drop; contract C5).
    /// The Tseitin state is always returned to its slot before `check`
    /// returns, so it is present here.
    pub(crate) fn model_view<'a>(&'a self, assertions: &'a [Assertion]) -> ModelView<'a> {
        ModelView {
            own: &*self.own,
            tseitin: self
                .tseitin
                .as_ref()
                .expect("Tseitin state is returned after every encode batch"),
            theory: &*self.theory,
            assertions,
            cfg: self.cfg,
        }
    }

    /// Via `tseitin.term_to_var`; `None` => fail closed.
    fn lit_of(&self, atom: TermId, value: bool) -> Option<Literal> {
        lit_of(self.tseitin.as_ref()?, atom, value)
    }

    fn atom_of(&self, lit: Literal) -> Option<(TermId, bool)> {
        let v = lit.variable().index();
        self.st
            .atom_of_var
            .get(v)
            .copied()
            .flatten()
            .map(|atom| (atom, lit.is_positive()))
    }

    /// The solve is over as far as the bridge is concerned (an exit is set);
    /// every further callback ends the solve without touching the theory.
    fn terminal(&self) -> bool {
        !matches!(self.exit, BridgeExit::None)
    }

    /// `Instant::now() >= deadline || (should_stop)()`.
    fn deadline_hit(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d) || (self.should_stop)()
    }

    /// Which budget a cooperative stop was (§3.5): the deadline if it has
    /// passed, memory if the store tripped, else the engine's interrupt flag.
    fn budget_kind(&self) -> BudgetKind {
        if self.deadline.is_some_and(|d| Instant::now() >= d) {
            BudgetKind::Deadline
        } else if TermStore::global_memory_exceeded() {
            BudgetKind::Memory
        } else {
            BudgetKind::Interrupted
        }
    }

    fn stop_for_budget(&mut self) {
        self.exit = BridgeExit::Budget(self.budget_kind());
        self.stats.deadline_stops += 1;
    }

    /// Negated conflict clause. `None` (=> exit `TheoryIncomplete`) on any
    /// unmapped atom or on a literal that is not TRUE on the SAT trail; an
    /// EMPTY theory conflict is `Poison(EmptyTheoryConflict)`. The clause is
    /// sorted and de-duplicated (a literal and its negation cannot both be
    /// true, so a tautology is rejected by the trail check).
    fn map_conflict(
        &mut self,
        ctx: &dyn SolverContext,
        lits: &[TheoryLit],
    ) -> Option<Vec<Literal>> {
        if lits.is_empty() {
            // INV-S5: a theory bug, poisoned (and counted), never a panic.
            self.exit = BridgeExit::Poison(PoisonKind::EmptyTheoryConflict);
            return None;
        }
        let num_vars = ctx.num_vars();
        let mut clause = Vec::with_capacity(lits.len());
        for l in lits {
            let Some(sat_lit) = self.lit_of(l.term, l.value) else {
                self.stats.unmapped_conflicts += 1;
                self.exit = BridgeExit::TheoryIncomplete;
                return None;
            };
            if sat_lit.variable().index() >= num_vars || ctx.lit_value(sat_lit) != Some(true) {
                self.stats.non_falsified_conflicts += 1;
                self.exit = BridgeExit::TheoryIncomplete;
                return None;
            }
            clause.push(sat_lit.negated());
        }
        clause.sort_unstable_by_key(|l| l.index());
        clause.dedup();
        Some(clause)
    }

    /// A theory conflict (BCP-time or final): map, record, count. `None` when
    /// the exit is already set by `map_conflict`.
    fn conflict_clause(
        &mut self,
        ctx: &dyn SolverContext,
        lits: &[TheoryLit],
        farkas: Option<FarkasAnnotation>,
        at_bcp: bool,
    ) -> Option<Vec<Literal>> {
        let clause = self.map_conflict(ctx, lits)?;
        self.ledger.record(
            self.epoch,
            LedgerKind::Conflict,
            lits,
            &clause,
            farkas,
            at_bcp,
        );
        self.stats.conflicts += 1;
        if at_bcp {
            self.stats.bcp_conflicts += 1;
        }
        Some(clause)
    }

    /// Feed `ctx.trail()[last_trail_pos..]` with per-literal scope alignment
    /// (§2.4 `feed_trail`), skipping non-atoms, inactive atoms and already-fed
    /// level-0 facts; clamps the cursor to the trail length first.
    ///
    /// For each literal `l` (var `v`, SAT level `L`) with `atom_of_var[v] =
    /// Some(a)` and `active_atom[v]`:
    /// - `L == 0` and the theory is at scope 0: feed at scope 0 once per
    ///   session (`l0_fed`); the incremental reset keeps the level-0 trail, so
    ///   these are permanent SAT facts and permanent theory facts;
    /// - else `while theory_level < L { flush; level_cursor.push(pos);
    ///   theory.push(); theory_level += 1 }` then
    ///   `theory.assert_literal(a, l.is_positive())`.
    ///
    /// The cursor recorded for scope `i` is the position of the FIRST literal
    /// fed at scope `>= i` (pre-feed), so `backtrack(k)` re-feeds exactly the
    /// literals from that position on — the popped suffix — and nothing below
    /// it is ever fed twice.
    ///
    /// SCOPE FLUSH (WP-2 finding, `lra_bounds_are_trailed_in_the_scope_of_the_check_repro`):
    /// `LraSolver` applies an atom's bounds lazily, at its next
    /// `check`/`check_during_propagate`, and trails them in the scope CURRENT
    /// AT THAT CHECK. ay-sat's assumption loop consults the extension only
    /// once every assumption is decided (F5), so without a flush the bridge
    /// would open scopes 1..n in one call and check once at scope n — every
    /// prefix bound would sit above scope n's mark, and the first backjump
    /// into the prefix would pop them while their atoms stay asserted (the
    /// theory then answers `Sat` for `x ∈ [0,0], x != y` with `x = -1/2`).
    /// ay-dpll never sees this because it gets one `propagate` per SAT level.
    /// So: before each `push`, if anything was fed at the current scope since
    /// the last theory check, run `check_during_propagate` (a conflict it
    /// finds is over fed literals at or below the current scope, all on the
    /// SAT trail — kept as `pending_conflict`, feeding stops at the current
    /// position and the caller returns the conflict instead of checking).
    fn feed_trail(&mut self, ctx: &dyn SolverContext) {
        let trail = ctx.trail();
        let n = trail.len();
        if self.last_trail_pos > n {
            self.last_trail_pos = n;
        }
        // A backjump to level `k >= theory_level` pops no theory scope, so the
        // cursor was not restored — yet the solver truncated its trail to the
        // end of level `k` and has since appended the learned clause's
        // asserting literal AT level `k` plus its propagations, where the
        // removed (level > k) literals used to sit. Rewind to the START of
        // level `k` and re-scan: literals above `k` were never fed (feeding one
        // would have pushed the theory past `k`), and level-`k` atoms already
        // fed in the current scope instance are skipped by `fed_gen` (WP-4
        // integration finding: fuzz script 21's `E ∨ ¬b, E ∨ b` assertion —
        // `E` asserted by the learned unit at the backjump level, one position
        // below the cursor, was never fed and the solve ended SAT with a model
        // violating it).
        if let Some(k) = self.trail_truncated_level.take() {
            let mut pos = self.last_trail_pos.min(n);
            while pos > 0
                && ctx
                    .var_level(trail[pos - 1].variable())
                    .is_some_and(|l| l >= k)
            {
                pos -= 1;
            }
            self.last_trail_pos = pos;
        }
        let st = &mut *self.st;
        st.grow(ctx.num_vars());
        let theory = self.theory.as_dyn();
        let mut fed_since_check = false;
        // Late activations (see `sticky`): feed at the current scope.
        if !st.late_activated.is_empty() {
            let late = std::mem::take(&mut st.late_activated);
            for v in late {
                let var = Variable::new(v);
                let (Some(value), Some(Some(atom))) =
                    (ctx.value(var), st.atom_of_var.get(v as usize).copied())
                else {
                    continue; // unassigned now: the ordinary trail feed takes it
                };
                let level = ctx.var_level(var).unwrap_or(0);
                if level == 0 && self.theory_level == 0 {
                    if !st.l0_fed[v as usize] {
                        st.l0_fed[v as usize] = true;
                        theory.assert_literal(atom, value);
                        fed_since_check = true;
                    }
                } else {
                    st.fed_gen[v as usize] = self.scope_gen.last().copied().unwrap_or(0);
                    theory.assert_literal(atom, value);
                    fed_since_check = true;
                    self.sticky.push((v, self.theory_level));
                }
                self.stats.late_feeds += 1;
                self.stats.fed_literals += 1;
            }
        }
        let mut pos = self.last_trail_pos;
        if super::session_trace() {
            let items: Vec<String> = trail[pos..n]
                .iter()
                .map(|l| {
                    let v = l.variable().index();
                    format!(
                        "{}{}@{:?}{}{}",
                        if l.is_positive() { "+" } else { "-" },
                        v + 1,
                        ctx.var_level(l.variable()),
                        if st.atom_of_var.get(v).copied().flatten().is_some() {
                            "a"
                        } else {
                            ""
                        },
                        if st.is_active(v) { "*" } else { "" }
                    )
                })
                .collect();
            ay_core::safe_eprintln!(
                "[CHC-SESSION-TRACE] feed_trail from={pos} n={n} theory_level={} dl={} trail={:?}",
                self.theory_level,
                ctx.decision_level(),
                items
            );
        }
        while pos < n {
            let lit = trail[pos];
            let var = lit.variable();
            let v = var.index();
            if let Some(Some(atom)) = st.atom_of_var.get(v).copied() {
                if st.active_atom[v] {
                    let level = ctx.var_level(var).unwrap_or_else(|| ctx.decision_level());
                    if level == 0 && self.theory_level == 0 {
                        if !st.l0_fed[v] {
                            st.l0_fed[v] = true;
                            theory.assert_literal(atom, lit.is_positive());
                            fed_since_check = true;
                            self.stats.fed_literals += 1;
                            self.stats.l0_feeds += 1;
                        }
                    } else {
                        if level < self.theory_level {
                            // Out-of-order trail (impossible with chronological
                            // backtracking off, the session profile): feed at
                            // the current, deeper scope. The theory may then
                            // forget the fact before SAT unassigns it — it only
                            // ever MISSES a fact this way (a weaker theory, the
                            // strict verifier's job), never invents one.
                            self.stats.out_of_order_feeds += 1;
                        }
                        while self.theory_level < level {
                            if fed_since_check {
                                fed_since_check = false;
                                self.stats.scope_flushes += 1;
                                let conflict = match theory.check_during_propagate() {
                                    TheoryResult::Unsat(lits) => Some((lits, None)),
                                    TheoryResult::UnsatWithFarkas(c) => {
                                        Some((c.literals, c.farkas))
                                    }
                                    _ => None,
                                };
                                if let Some(conflict) = conflict {
                                    // Stop here: this literal and the rest of the
                                    // trail are re-fed after the backjump.
                                    self.stats.scope_flush_conflicts += 1;
                                    self.pending_conflict = Some(conflict);
                                    self.last_trail_pos = pos;
                                    return;
                                }
                            }
                            // The cursor of the new scope is where its SAT LEVEL
                            // begins on the trail, not where this atom sits: a
                            // backjump truncates the trail to the end of the
                            // kept level and the solver then appends the learned
                            // clause's literal (and its propagations) at the
                            // positions the popped level's NON-atom prefix
                            // (assumption, root literal, ...) used to occupy.
                            // With the atom's position as cursor those new
                            // literals sat below the restored cursor and were
                            // never fed — a theory atom implied right after the
                            // backjump went unseen and the solve ended SAT with
                            // a model violating it (WP-4 push/pop fuzz: 3 % of
                            // checks demoted, `or-shape` repro in
                            // `pushpop_fuzz.rs`). Walk back over the (short)
                            // level prefix: the trail is level-sorted.
                            let target = self.theory_level + 1;
                            let mut start = pos;
                            while start > 0
                                && ctx
                                    .var_level(trail[start - 1].variable())
                                    .is_some_and(|l| l >= target)
                            {
                                start -= 1;
                            }
                            self.level_cursor.push(start);
                            st.gen_counter = st.gen_counter.wrapping_add(1).max(1);
                            self.scope_gen.push(st.gen_counter);
                            theory.push();
                            self.theory_level += 1;
                            self.stats.theory_pushes += 1;
                        }
                        let scope_generation = self.scope_gen.last().copied().unwrap_or(0);
                        if scope_generation != 0 && st.fed_gen[v] == scope_generation {
                            // Already fed in this very scope instance (a
                            // re-scan after a backjump rewind).
                            self.stats.rescanned_fed += 1;
                        } else {
                            st.fed_gen[v] = scope_generation;
                            theory.assert_literal(atom, lit.is_positive());
                            fed_since_check = true;
                            self.stats.fed_literals += 1;
                        }
                    }
                }
            }
            pos += 1;
        }
        self.last_trail_pos = n;
    }

    /// `theory.propagate()` -> EAGER `propagations.push((reason_clause, lit))`
    /// with `reason_clause = [lit, ¬r1, …, ¬rk]`; a lazy propagation is
    /// materialised through `explain_propagation` first; unmapped => dropped;
    /// each reason clause is recorded in the ledger as `LedgerKind::Propagation`.
    /// A target already FALSE on the trail turns the reason clause into a
    /// conflict (all literals false), returned immediately.
    fn drain_propagations(&mut self, ctx: &dyn SolverContext, out: &mut ExtPropagateResult) {
        let num_vars = ctx.num_vars();
        let props = self.theory.as_dyn().propagate();
        for p in props {
            let Some(target) = self.lit_of(p.literal.term, p.literal.value) else {
                self.stats.dropped_propagations += 1;
                continue;
            };
            if target.variable().index() >= num_vars {
                // Minted this check, not yet in the solver (unreachable in
                // practice: every minted var is in a returned clause).
                self.stats.dropped_propagations += 1;
                continue;
            }
            let target_value = ctx.lit_value(target);
            if target_value == Some(true) {
                // Already implied by BCP: redundant.
                continue;
            }
            let reason: Vec<TheoryLit> = if !p.reason.is_empty() {
                p.reason
            } else if let Some(rd) = p.reason_data {
                match self.theory.as_dyn().explain_propagation(p.literal.term, rd) {
                    Some(r) if !r.is_empty() => r,
                    _ => {
                        self.theory
                            .as_dyn()
                            .mark_propagation_rejected(p.literal.term, rd);
                        self.stats.dropped_propagations += 1;
                        continue;
                    }
                }
            } else {
                self.stats.dropped_propagations += 1;
                continue;
            };
            let mut clause = Vec::with_capacity(reason.len() + 1);
            clause.push(target);
            let mut ok = true;
            for r in &reason {
                match self.lit_of(r.term, !r.value) {
                    Some(l)
                        if l.variable().index() < num_vars
                            && l.variable() != target.variable()
                            && ctx.lit_value(l) == Some(false) =>
                    {
                        clause.push(l);
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                self.stats.dropped_propagations += 1;
                continue;
            }
            let mut lits = reason;
            lits.push(TheoryLit::new(p.literal.term, !p.literal.value));
            self.ledger.record(
                self.epoch,
                LedgerKind::Propagation,
                &lits,
                &clause,
                None,
                true,
            );
            if target_value == Some(false) {
                // Every literal of the reason clause is false: a conflict.
                self.stats.propagation_conflicts += 1;
                self.stats.conflicts += 1;
                out.bump_vars = clause.iter().map(|l| l.variable()).collect();
                out.conflict = Some(clause);
                out.propagations.clear();
                return;
            }
            self.stats.propagations += 1;
            out.propagations.push((clause, target));
        }
    }

    /// Disjoint borrows of the parts a mint batch mutates.
    fn minter<'a>(&'a mut self, ctx: &'a dyn SolverContext) -> Minter<'a> {
        Minter::new(
            &mut *self.theory,
            &mut *self.own,
            &mut *self.tseitin,
            &mut *self.st,
            &mut *self.ledger,
            &mut self.mint,
            self.cfg,
            &mut self.stats,
            ctx,
        )
    }

    /// Map one theory `check()` result to the solver's answer (the body of
    /// `Extension::check`). `recheck_hints`: see [`Self::answer_model_eqs`].
    fn answer_theory(
        &mut self,
        ctx: &dyn SolverContext,
        result: TheoryResult,
        recheck_hints: bool,
    ) -> ExtCheckResult {
        match result {
            TheoryResult::Sat => {
                self.last_request = None;
                self.repeat_count = 0;
                ExtCheckResult::Sat
            }
            TheoryResult::Unsat(lits) => match self.conflict_clause(ctx, &lits, None, false) {
                Some(clause) => ExtCheckResult::Conflict(clause),
                None => ExtCheckResult::Unknown,
            },
            TheoryResult::UnsatWithFarkas(c) => {
                match self.conflict_clause(ctx, &c.literals, c.farkas, false) {
                    Some(clause) => ExtCheckResult::Conflict(clause),
                    None => ExtCheckResult::Unknown,
                }
            }
            TheoryResult::NeedDisequalitySplit(req) => {
                // Batched: the theory buffers the other violated single-var
                // disequalities of the same scan (#8762).
                let mut reqs = vec![req];
                reqs.extend(self.theory.as_dyn().drain_pending_diseq_splits());
                let outcome = self.minter(ctx).diseq_splits(reqs);
                self.answer_mint(ctx, outcome)
            }
            TheoryResult::NeedExpressionSplit(req) => {
                let outcome = self.minter(ctx).expr_splits(vec![req]);
                self.answer_mint(ctx, outcome)
            }
            TheoryResult::NeedExpressionSplits(reqs) => {
                let outcome = self.minter(ctx).expr_splits(reqs);
                self.answer_mint(ctx, outcome)
            }
            TheoryResult::NeedModelEquality(req) => {
                self.answer_model_eqs(ctx, vec![req], recheck_hints)
            }
            TheoryResult::NeedModelEqualities(reqs) => {
                self.answer_model_eqs(ctx, reqs, recheck_hints)
            }
            TheoryResult::NeedLemmas(lemmas) => {
                let outcome = self.minter(ctx).lemmas(lemmas);
                self.answer_mint(ctx, outcome)
            }
            TheoryResult::NeedSplit(_) => {
                // Persistent sessions are LRA-only. They do not mint integer
                // branch-and-bound splits.
                self.exit = BridgeExit::Unsupported(UnsupportedKind::Shape);
                ExtCheckResult::Unknown
            }
            TheoryResult::NeedStringLemma(_) => {
                self.exit = BridgeExit::Unsupported(UnsupportedKind::Shape);
                ExtCheckResult::Unknown
            }
            TheoryResult::Unknown => self.unknown_exit(),
            // `TheoryResult` is `#[non_exhaustive]`.
            _ => {
                self.exit = BridgeExit::Unsupported(UnsupportedKind::Shape);
                ExtCheckResult::Unknown
            }
        }
    }

    /// A model-equality round. When it mints nothing new and `recheck` is set,
    /// the theory is asked once more WITHOUT LRA's `assume_eqs`-over-split
    /// preference before the hint round may converge to `Sat` (§4.3).
    ///
    /// Rung-4 finding (om1relays replay, 7 router demotions): LRA answers a
    /// VIOLATED multi-variable disequality with model-value equality guesses
    /// instead of its expression split (`theory_solver/check.rs`, #8707).
    /// Once every guessed pair is minted the round is "nothing new", but the
    /// disequality is still violated; converging to `Sat` handed the router
    /// a model its strict evaluation of the original expression rejected.
    /// Re-asked without the preference, a violation comes back as its split
    /// (minted as usual, the search moves); a genuine hint round — ITE links,
    /// post-`Sat` `assume_eqs` — comes back as hints again and converges.
    fn answer_model_eqs(
        &mut self,
        ctx: &dyn SolverContext,
        reqs: Vec<ay_core::ModelEqualityRequest>,
        recheck: bool,
    ) -> ExtCheckResult {
        let outcome = self.minter(ctx).model_equalities(reqs);
        if recheck && matches!(outcome, Ok(MintOutcome::NothingNew)) {
            self.stats.hint_rechecks += 1;
            self.theory.rebind(self.own);
            self.theory.set_assume_eqs_over_split(false);
            let again = self.theory.as_dyn().check();
            self.theory.set_assume_eqs_over_split(true);
            return self.answer_theory(ctx, again, false);
        }
        self.answer_mint(ctx, outcome)
    }

    /// Turn a mint outcome into the `check()` answer (§2.4 `check`, §4).
    fn answer_mint(
        &mut self,
        ctx: &dyn SolverContext,
        outcome: Result<MintOutcome, BridgeExit>,
    ) -> ExtCheckResult {
        let outcome = match outcome {
            Ok(o) => o,
            Err(exit) => {
                self.exit = exit;
                return ExtCheckResult::Unknown;
            }
        };
        if self.mint.count > self.cfg.max_mints_per_query {
            self.exit = BridgeExit::Budget(BudgetKind::MintCap);
            return ExtCheckResult::Unknown;
        }
        match outcome {
            MintOutcome::Inline(clauses) => {
                debug_assert!(
                    clauses.iter().all(|c| !c.is_empty()),
                    "an inline batch never carries an empty clause (F6)"
                );
                if clauses.is_empty() {
                    // Nothing to add would livelock the loop (B-lifetime m3).
                    self.exit = BridgeExit::TheoryIncomplete;
                    return ExtCheckResult::Unknown;
                }
                if self.tripwire(ctx, &clauses) {
                    self.exit = BridgeExit::TheoryIncomplete;
                    return ExtCheckResult::Unknown;
                }
                self.stats.inline_batches += 1;
                self.stats.inline_clauses += clauses.len() as u64;
                ExtCheckResult::AddClauses(clauses)
            }
            MintOutcome::Originals => {
                // Tier 2 (§4.2). The buffered clauses name FRESH variables
                // that only `add_theory_lemma` grows the solver for;
                // `add_clause_global` (the session's path for originals)
                // does not, so the batch is ALSO handed to ay-sat inline:
                // the solver grows, the deletable copies are subsumed by the
                // originals the session adds, and the exit makes the very
                // next `propagate()` stop the solve (`terminal`) so the
                // session re-enters with the originals in place.
                self.stats.originals_restarts += 1;
                self.stats.originals_clauses = self.mint.originals.len() as u64;
                self.exit = BridgeExit::RestartWithOriginals;
                ExtCheckResult::AddClauses(self.mint.originals.clone())
            }
            MintOutcome::NothingNew => {
                // Hint convergence (§4.3): hints are not refutations; the
                // strict verifier judges the accepted model.
                self.stats.hint_convergences += 1;
                ExtCheckResult::Sat
            }
        }
    }

    /// §4.1 loop protection: the same inline batch answered with the SAT state
    /// unchanged (same trail length, same conflict count) `REQUEST_REPEAT_TRIP`
    /// times in a row. A legitimate re-request always moves the search (the
    /// re-added clause is a pending conflict or a unit), so the state changes.
    fn tripwire(&mut self, ctx: &dyn SolverContext, clauses: &[Vec<Literal>]) -> bool {
        let mut key: Vec<Vec<Literal>> = clauses.to_vec();
        for c in &mut key {
            c.sort_unstable_by_key(|l| l.index());
        }
        key.sort();
        let state = (ctx.trail().len(), ctx.conflicts());
        let same = self
            .last_request
            .as_ref()
            .is_some_and(|(k, t, c)| *k == key && *t == state.0 && *c == state.1);
        if same {
            self.repeat_count += 1;
        } else {
            self.repeat_count = 1;
            self.last_request = Some((key, state.0, state.1));
        }
        if self.repeat_count >= REQUEST_REPEAT_TRIP {
            self.stats.tripwire_trips += 1;
            return true;
        }
        false
    }

    /// The final-check answer for a theory `Unknown` (§3.5): a stop that is
    /// due is `Budget`, never `TheoryIncomplete`.
    fn unknown_exit(&mut self) -> ExtCheckResult {
        if self.deadline_hit() {
            self.stop_for_budget();
        } else {
            self.exit = BridgeExit::TheoryIncomplete;
        }
        ExtCheckResult::Unknown
    }
}

/// The fail-closed atom -> literal map (ay-dpll `extension/helpers.rs`
/// `term_to_literal`, plus the encoder's polarity cache for terms it named
/// without a variable of their own, e.g. a `Not` atom).
pub(crate) fn lit_of(ts: &TseitinState, atom: TermId, value: bool) -> Option<Literal> {
    if let Some(&dimacs_var) = ts.term_to_var.get(&atom) {
        let var = Variable::new(dimacs_var.checked_sub(1)?);
        return Some(if value {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        });
    }
    if let Some(&c) = ts.encoded.get(&(atom, true)) {
        let lit = Literal::from_dimacs(c);
        return Some(if value { lit } else { lit.negated() });
    }
    if let Some(&c) = ts.encoded.get(&(atom, false)) {
        // `encode(t, false)` names ¬t.
        let lit = Literal::from_dimacs(c);
        return Some(if value { lit.negated() } else { lit });
    }
    None
}

impl Extension for TheoryBridge<'_> {
    fn init(&mut self) {
        // NO theory reset (F5: called once per solve; the theory was popped to
        // scope 0 by the previous query's drop guard). The incremental reset
        // keeps the level-0 trail; `l0_fed` skips re-feeds.
        self.stats.solves += 1;
        self.last_trail_pos = 0;
        self.level_cursor.clear();
        self.scope_gen.clear();
        self.sticky.clear();
        self.st.late_activated.clear();
        self.trail_truncated_level = None;
        self.last_request = None;
        self.repeat_count = 0;
        self.pending_conflict = None;
        self.mint.begin_solve();
        // Align the theory with the solver's fresh solve. ay-sat's incremental
        // reset drops the SAT trail above level 0 WITHOUT an `ext.backtrack`
        // (F5 lists the conflict-analysis and partial-restart sites only), so
        // at a RE-ENTRY (§4.2) the theory is legitimately still at the scope
        // where the previous solve stopped; between queries the guard's
        // `backtrack(0)` already brought it to 0. Pop whatever is left.
        if self.theory_level != 0 {
            self.stats.init_pops += 1;
            while self.theory_level > 0 {
                self.theory.as_dyn().pop();
                self.theory_level -= 1;
                self.stats.theory_pops += 1;
            }
        }
        self.exit = BridgeExit::None;
        self.st.refresh_minted_activity();
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        // A terminal exit set at init must end the solve at the first
        // opportunity (propagate returns `stop`).
        self.terminal()
            || ctx.trail().len() > self.last_trail_pos
            || self.theory.as_dyn_ref().has_pending_propagations()
    }

    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        self.stats.propagate_calls += 1;
        if self.terminal() {
            return ExtPropagateResult::none().with_stop(true);
        }
        if self.deadline_hit() {
            self.stop_for_budget();
            return ExtPropagateResult::none().with_stop(true);
        }
        self.feed_trail(ctx);
        // The BCP-time check (sound-but-weaker contract). `Sat`/`Need*`/
        // `Unknown` fall through: requests are re-derived by the final check
        // (LRA's BCP-time check raises no disequality work anyway) and its
        // `Unknown` is not a verdict (module doc). A conflict a scope flush
        // found inside `feed_trail` takes its place.
        let result = match self.pending_conflict.take() {
            Some((lits, farkas)) => match farkas {
                Some(f) => {
                    TheoryResult::UnsatWithFarkas(ay_core::TheoryConflict::with_farkas(lits, f))
                }
                None => TheoryResult::Unsat(lits),
            },
            None => self.theory.as_dyn().check_during_propagate(),
        };
        match result {
            TheoryResult::Unsat(lits) => {
                return match self.conflict_clause(ctx, &lits, None, true) {
                    Some(clause) => {
                        let bump: Vec<Variable> = clause.iter().map(|l| l.variable()).collect();
                        ExtPropagateResult::conflict(clause).with_bump_vars(bump)
                    }
                    None => ExtPropagateResult::none().with_stop(true),
                };
            }
            TheoryResult::UnsatWithFarkas(c) => {
                return match self.conflict_clause(ctx, &c.literals, c.farkas, true) {
                    Some(clause) => {
                        let bump: Vec<Variable> = clause.iter().map(|l| l.variable()).collect();
                        ExtPropagateResult::conflict(clause).with_bump_vars(bump)
                    }
                    None => ExtPropagateResult::none().with_stop(true),
                };
            }
            TheoryResult::Unknown => {
                self.stats.bcp_unknowns += 1;
            }
            _ => {}
        }
        let mut out = ExtPropagateResult::none();
        self.drain_propagations(ctx, &mut out);
        out
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.stats.check_calls += 1;
        if self.terminal() {
            return ExtCheckResult::Unknown;
        }
        if self.deadline_hit() {
            self.stop_for_budget();
            return ExtCheckResult::Unknown;
        }
        self.feed_trail(ctx);
        let result = match self.pending_conflict.take() {
            Some((lits, farkas)) => match farkas {
                Some(f) => {
                    TheoryResult::UnsatWithFarkas(ay_core::TheoryConflict::with_farkas(lits, f))
                }
                None => TheoryResult::Unsat(lits),
            },
            None => self.theory.as_dyn().check(),
        };
        self.answer_theory(ctx, result, true)
    }

    fn backtrack(&mut self, new_level: u32) {
        // Tolerates new_level > theory_level (the partial restart passes
        // assumptions.len(), an INDEX count, F5). The cursor is clamped to the
        // trail length at the top of `feed_trail`, and rewound below every
        // literal above `new_level` there (`trail_truncated_level`).
        // (ay-dpll `extension/mod.rs` backtrack loop.)
        self.trail_truncated_level = Some(
            self.trail_truncated_level
                .map_or(new_level, |l| l.min(new_level)),
        );
        if !self.sticky.is_empty() {
            // Entries fed at a scope that is being popped leave the theory; the
            // ones the SAT trail still holds (their level is <= new_level, which
            // `feed_trail` re-checks through `ctx.value`) are fed again at the
            // next feed. Entries fed at or below `new_level` stay.
            let st = &mut *self.st;
            self.sticky.retain(|&(v, fed_at)| {
                if fed_at > new_level {
                    st.late_activated.push(v);
                    false
                } else {
                    true
                }
            });
        }
        while self.theory_level > new_level {
            self.theory.as_dyn().pop();
            self.theory_level -= 1;
            self.stats.theory_pops += 1;
            self.last_trail_pos = self.level_cursor.pop().unwrap_or(0);
            self.scope_gen.pop();
        }
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        if let Some(&phase) = self.st.preferred_phase.get(&var.id()) {
            return Some(phase);
        }
        let v = var.index();
        if !self.st.is_active(v) {
            return None;
        }
        let atom = self.st.atom_of_var.get(v).copied().flatten()?;
        self.theory.as_dyn_ref().suggest_phase(atom)
    }

    fn seed_phase_hints_dual(&self, _phase: &mut [i8], _target_phase: &mut [i8], _vals: &[i8]) {
        // No-op in Rung 1 (no bulk O(#atoms) scan per quiescence, §6.2 item 4).
    }

    fn explain_lazy_reason(
        &mut self,
        _propagated: Literal,
        _reason_data: u64,
    ) -> Option<Vec<Literal>> {
        // Never emitted: the bridge uses eager reasons only (ay-sat test t4).
        None
    }

    fn on_restart(&self) -> Vec<Variable> {
        // ACTIVE theory atom vars only.
        self.st
            .atom_of_var
            .iter()
            .enumerate()
            .filter(|(v, atom)| atom.is_some() && self.st.is_active(*v))
            .map(|(v, _)| Variable::new(v as u32))
            .collect()
    }

    fn suggest_decision(&self, _ctx: &dyn SolverContext) -> Option<Literal> {
        // Rung 1: VSIDS only.
        None
    }
}

#[cfg(test)]
#[path = "tests/bridge_unit.rs"]
mod bridge_unit;
