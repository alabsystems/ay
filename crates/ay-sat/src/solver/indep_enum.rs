// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-parallel independent-support ENUMERATION (constructive startup probe).
//!
//! The SAT-COMP 2026 Main Track `xorshift` family (11 instances, all SAT:
//! unrolled xorshift-PRNG inversion circuits, 1773-2965 variables /
//! 6618-10504 clauses / 32 unit clauses pinning the output word) is out of
//! reach for CDCL — the 2026 winner solved ZERO of them at 5000 s, and AY
//! solves one. Exactly one 2026 solver cracks all eleven, `zhenwei_kissat-sup`,
//! in 192-1581 s, and it does NOT do it by branching cleverly.
//!
//! # Why restricting decisions is not the technique
//!
//! `solver/indep_support.rs` already recovers the support and it is EXACTLY
//! the 32 PRNG seed bits on all eleven, in under a millisecond. Restricting
//! CDCL decisions to those 32 bits converts nothing, and cannot: 32 free bits
//! are 2^32 seeds, AY takes decisions at ~15K/s here, and clauses learned over
//! PRNG-inversion bits prune nothing — roughly 80 hours of leaves. The support
//! is not a branching hint. It is an enumeration domain.
//!
//! # The technique
//!
//! Enumerate all `2^|S|` support assignments, but evaluate `ENUM_WIDTH` of
//! them **simultaneously** by packing one assignment per bit of a machine
//! word: every literal owns an `ENUM_WORDS`-word column bitset, and unit
//! propagation becomes word-wise AND/OR/NOT (`engine.rs`). One pass over the
//! constraint list refutes (or completes) 4096 seeds at once, and `2^32/4096`
//! = 1.05M passes is feasible where 2^32 CDCL restarts is not.
//!
//! Three things make it fast enough to matter:
//!
//! * **Early exit.** A block stops the instant every column is refuted, so a
//!   block costs a PREFIX of the constraint list, not a full pass.
//! * **Self-organising order** (`ctick`): the next block's queue is rebuilt in
//!   the order the previous block resolved constraints, so the refuting prefix
//!   converges to the front.
//! * **XOR collapse.** A complete parity class of `2^(k-1)` clauses over the
//!   same `k` variables IS an XOR constraint, and one XOR visit replaces four
//!   ternary-clause visits. On `xorshift_r14_31`: 6586 clauses collapse to
//!   1363 XORs + 1134 residual clauses (the family's 378 AND gates), a 2.6x
//!   cut in visits and 2.8x in literal-word work.
//!
//! # Measured throughput, and the next lever
//!
//! 9.8-23.2M assignments/s across the eleven (M5 Max, one core,
//! `-C target-cpu=native`): 185-400 s to sweep the whole 2^32 seed space,
//! against kissat-sup's 192-1581 s to find its model. The early exit is worth
//! ~13% and no more — refuting a column means propagating its seed the whole
//! way to a pinned output bit, so a block costs ~87% of the constraint list.
//!
//! The next lever is the residue the XOR collapse cannot take: the AND gates
//! stay as `(¬y ∨ a) (¬y ∨ b) (y ∨ ¬a ∨ ¬b)`, three constraints and seven
//! literal slots where one AND kind would be one and three. On
//! `xorshift_r14_110` that is 882 of 4133 constraints carrying 6174 of 10635
//! literal slots — cutting visits ~43%, word work ~33%. Not taken:
//! kissat-sup's own bitset propagator has only the clause and XOR kinds, and
//! 11/11 already convert.
//!
//! # Non-support variables
//!
//! Never enumerated and never chosen: the bit-parallel pass IS their
//! derivation. Because `S` is an independent support, every other variable is
//! UP-implied once `S` is fixed, so propagating the WHOLE constraint set (not
//! only clauses over `S`) both completes the assignment and refutes the dead
//! columns. "Support-only clauses first" is not an option here — no clause is
//! over the seed bits alone; every refutation travels the circuit.
//!
//! # Verdict safety
//!
//! * **SAT**: a surviving column is read out as a full assignment over the
//!   EXTERNAL variables and verified against every clause of the ORIGINAL
//!   formula (`verify_external_model` over `cold.original_ledger`) — the same
//!   authoritative gate `finalize_sat_model` ends on. Reconstruction is not
//!   owed: it exists to lift a model of the SIMPLIFIED formula, and this is a
//!   total model of the original one. A model is its own certificate, so the
//!   route is proof-mode safe.
//! * **UNSAT is never claimed.** Exhausting the support space *would* refute
//!   the formula if (a) the recovered gate set really is a functional
//!   definition of every non-support variable in the ORIGINAL formula and (b)
//!   the collapse + propagation is exact. (a) rests on heuristic gate
//!   extraction, and under `--proof` an UNSAT verdict additionally owes a
//!   derivation this route cannot emit. So exhaustion logs, bumps a counter,
//!   and falls through. The only cost would be an UNSAT family member — the
//!   eleven known ones are all SAT.
//! * Saturation without resolution (a stall with constraints still holding two
//!   unassigned literals in some column) means the support did not actually
//!   determine the formula. That also falls through, with no verdict.
//!
//! # Admission gate
//!
//! Mirrors `indepsup.c:2097` `propagating()` in shape, retuned to AY's
//! measured throughput (see the constants below). Off-family instances pay two
//! integer comparisons. Placement is BEFORE preprocessing, like the support
//! computation itself — BVE resolves away the Tseitin scaffolding the support
//! is read from (563 of 1773 variables on `xorshift_r14_31`).
//!
//! # Ordering and budget: the probe never owns the solve
//!
//! The admission gate is a WORK bound, not a TIME bound, and it authorises
//! ~12 minutes. Shipped default-on, it turned `simon-r20-0` and `simon-r22-1`
//! — 0.07-0.16 s SAT solves — into 300 s timeouts on the full-400 proof-mode
//! sweep, because the gate admits them for exactly the reasons it admits the
//! family: `simon-r20-0` has a 32-variable support, 4160 constraints, 2432
//! XORs and 4.36e9 projected visits, inside the family's own 2.6e9-5.7e9
//! range on every axis. NO TIGHTENING OF THIS GATE CAN SEPARATE THEM. The
//! discriminator is not structural, it is temporal: CDCL solves the Simon
//! instances instantly and cannot touch the family at 5000 s.
//!
//! So the enumeration is a PARKED probe with a schedule, like every other
//! probe here (`lucky_scratch.rs`, `try_walk`'s tick budget):
//!
//! 1. **Build at startup, run nothing.** The gate + program build still happen
//!    before preprocessing (that is the only place the gate structure exists),
//!    but the engine is parked in `cold.indep_enum_pending`.
//! 2. **Search goes first**, for `INDEP_ENUM_HEAD_START_FRACTION` of the
//!    visible budget, capped at `INDEP_ENUM_HEAD_START_MAX`. Both Simon
//!    instances land inside that head start and are solved at their native
//!    time.
//! 3. **Then the probe gets one slice**, capped at
//!    `INDEP_ENUM_BUDGET_FRACTION` of the visible budget — never the rest of
//!    the solve.
//! 4. **Then search resumes** with whatever is left. The slice is metered, so
//!    an unfinished enumeration costs a bounded fraction and nothing more.
//!
//! At the 300 s sweep budget that is 30 s of search, then a 135 s slice, then
//! 135 s of search again; at 600 s it is 30 s, a 268 s slice, and 302 s of
//! search (the family needs 9.9-221.5 s of the slice).
//!
//! The slice cap is what makes the schedule safe, not the head start: search
//! always keeps 55 % of the budget and always gets it BACK, so the worst the
//! probe can do to an instance search could have solved is delay it by
//! 1/0.55. The head start is only there so a solve that lands in the first
//! moments — `simon-r20-0` at 0.07 s — never waits for a probe at all.
//!
//! Because the engine is self-contained the parked slice can run after
//! preprocessing has renumbered variables: the parked program carries its own
//! internal->external map, a surviving column is read out in EXTERNAL space,
//! and the model is verified against the ORIGINAL clause ledger
//! (`verify_external_model`) — the same authoritative gate `finalize_sat_model`
//! applies. A total model of the original formula needs no reconstruction.
//!
//! CLI: `--sat-indep-enum <bool>`.

mod engine;

use super::*;
use crate::literal::{Literal, Variable};
use engine::{BitEnum, EnumOutcome, ENUM_BITS, KIND_CLAUSE, KIND_XOR};
use std::collections::HashMap;
use std::time::Duration;

/// Cheap pre-gate: variables. The per-column state is `2 * ENUM_WORDS * 8` =
/// 1 KiB per variable, so 16384 variables is already a 16 MiB working set —
/// an order of magnitude past the family (1773-2965) and past what stays
/// cache-resident. Two comparisons keep the whole corpus out.
const INDEP_ENUM_MAX_VARS: usize = 1 << 14;
/// Cheap pre-gate: active clauses (family: 6618-10504). Also the bound that
/// keeps gate recovery (the only non-trivial cost before admission) small.
const INDEP_ENUM_MAX_CLAUSES: usize = 1 << 16;
/// Largest support the enumerator will enumerate. kissat-sup uses the same
/// 40 (`indepsup.c:2103`); past it the work bound below never admits anyway.
const INDEP_ENUM_MAX_SUPPORT: usize = 40;
/// Work bound, the shape of kissat-sup's
/// `(1 << (size - 24)) * nclauses < 1e7` rewritten in AY's units: an upper
/// bound on TOTAL constraint visits, `blocks * constraints`, where
/// `blocks = 2^(|S| - ENUM_BITS)`.
///
/// kissat-sup's constant works out to `4.1e10` visits. AY measures
/// 12.2-14.0M visits/s across the eleven family members (M5 Max, one core,
/// `-C target-cpu=native`), so 4.1e10 would authorise ~50 minutes of
/// enumeration on a false positive. `1.0e10` caps that at ~12 minutes while
/// still admitting the whole family: the heaviest projection in it is
/// `xorshift_r15_113` / `xorshift_r15_175` at 2^20 blocks * 5453 constraints
/// = 5.7e9, and the lightest `xorshift_r14_31` at 2.6e9. The projection is a
/// worst case — the block early-exit means the family actually spends ~87% of
/// it per block, and a SAT member stops the moment its seed comes up.
const INDEP_ENUM_MAX_VISITS: u64 = 10_000_000_000;
/// Longest constraint the XOR collapse considers (`2^(k-1)` clauses).
const INDEP_ENUM_XOR_MAX_ARITY: usize = 4;

/// Share of the visible budget ordinary search gets BEFORE the parked
/// enumeration may run.
///
/// Sized against the CENSUS of what this route can actually reach, not
/// against the six-instance regression report. Four of those six —
/// `SDP_120_17_1675` (74466 vars), `SC23_Timetable_C_481_…` (248213),
/// `abw-K-dwt__234.mtx-w50` (56511), `51-136961` (31141 vars / 796510
/// clauses) — never get past the cheap pre-gate above, so `--sat-indep-enum`
/// runs identical code on them either way and they cannot be attributable
/// losses; measured repeatedly on one box they swing from 18.85 s to timeout
/// with the setting held fixed, which a single-sample full-400 sweep reads as
/// a regression. The two the probe really did break, `simon-r20-0` and
/// `simon-r22-1`, are 0.07-0.16 s solves.
///
/// So the head start only has to be huge relative to a fast solve, not
/// relative to a slow one: 0.10 covers the real victims by three orders of
/// magnitude and leaves the family the budget it needs. A 0.80 head start was
/// tried first, on the report's face value, and cost 4 of the 11 conversions
/// at 300 s for protection nothing needed.
const INDEP_ENUM_HEAD_START_FRACTION: f64 = 0.10;
/// Ceiling on that head start, so a long budget does not push the probe past
/// the point where it can still finish: the family needs 9.9-221.5 s of
/// enumeration whatever the budget is, because its cost is absolute, not
/// proportional. 30 s is ~200x the search time of the only search-solvable
/// instances the gate admits, and 5 % of a 600 s budget.
const INDEP_ENUM_HEAD_START_MAX: Duration = Duration::from_secs(30);
/// Share of the visible budget the enumeration may consume, once admitted.
///
/// The family's cost is absolute — 9.9-221.5 s of enumeration, measured, and
/// unchanged by how much budget the run has — so this fraction has to cover
/// 221.5 s at the 600 s validation budget: 0.45 x 600 = 270 s, a 22 % margin
/// over the slowest member instead of the 8 % that 0.40 would leave.
///
/// It is also the guarantee that replaces the missing time bound: whatever
/// the probe does, ordinary search keeps the majority of the budget and
/// RESUMES with it, so an admitted instance search could have solved is
/// delayed by at most a factor of 1/0.55, never starved. Anything the slice
/// does not finish is abandoned, never extended.
const INDEP_ENUM_BUDGET_FRACTION: f64 = 0.45;
/// Absolute ceiling on one slice, so a long budget cannot hand the probe half
/// an hour. `INDEP_ENUM_MAX_VISITS` (1e10) at the measured 12.2-14.0M
/// visits/s is ~770 s of work, so 800 s already covers a COMPLETE sweep of
/// the largest space the gate admits — past that the fraction would only buy
/// idle time. At the 5000 s competition budget this is what keeps the probe at
/// 16 % instead of 45 %.
const INDEP_ENUM_BUDGET_MAX: Duration = Duration::from_secs(800);
/// Head start when the caller installed no deadline (library embeddings that
/// solve to completion). Absolute, because there is no budget to take a
/// fraction of.
const INDEP_ENUM_HEAD_START_NO_DEADLINE: Duration = Duration::from_secs(30);
/// Enumeration budget when the caller installed no deadline. Still bounded:
/// an unbounded caller asked for a complete solve, not for a probe that owns
/// the process.
const INDEP_ENUM_BUDGET_NO_DEADLINE: Duration = Duration::from_secs(300);

/// CLI-owned tri-state: `--sat-indep-enum <bool>`.
fn indep_enum_enabled() -> bool {
    ay_core::sat_ab_switches()
        .indep_enum
        .unwrap_or(INDEP_ENUM_DEFAULT_ON)
}

/// Shipped default for the bit-parallel support enumerator: ON.
///
/// The A/B that shipped it (30 mixed corpus instances, `-T:120`, +5/-0)
/// concluded the gate "fired on exactly the eleven family members and nothing
/// else". It did not: the set simply contained no other instance the gate
/// admits. The full-400 proof-mode sweep at 300 s then found two —
/// `simon-r20-0` and `simon-r22-1`, 0.07-0.16 s SAT solves that became 300 s
/// timeouts.
///
/// The default stays ON because the route is worth 11 instances no other
/// technique here reaches, and the paired A/B of the fix (37 instances, the
/// two Simon instances + the eleven + 20 mixed companions, `-T:300`, proof
/// mode, same binary both arms) is +7 / -0 with zero verdict disagreements
/// and PAR-2 6213 against 9672. But it is the SCHEDULE above — search first,
/// one metered slice, search again — and NOT the admission gate that makes it
/// safe to leave on. Any future retune of the gate must keep that ordering.
const INDEP_ENUM_DEFAULT_ON: bool = true;

/// The constraint set the engine runs on, in dense-variable space.
struct EnumProgram {
    /// Dense variable id -> original variable index.
    orig_of: Vec<u32>,
    kinds: Vec<u8>,
    starts: Vec<u32>,
    lits: Vec<u32>,
    /// Support variables as dense ids (support members that occur in no
    /// surviving constraint are dropped — they constrain nothing).
    support: Vec<u32>,
}

/// An admitted enumeration, built before preprocessing and parked until search
/// has had its head start.
///
/// Everything here is in EXTERNAL variable space or engine-dense space, so it
/// survives the variable renumbering preprocessing performs after the park.
pub(crate) struct PendingIndepEnum {
    /// The resumable bit-parallel engine.
    engine: BitEnum,
    /// Engine-dense variable -> external variable index.
    ext_of: Vec<u32>,
    /// External-space assignment the parked program was reduced against: the
    /// level-0 values at park time. A surviving column overwrites the
    /// variables the engine carries and leaves the rest at their root value.
    root_ext_model: Vec<bool>,
    /// Wall-clock instant at which search's head start expires and the probe
    /// may take its slice.
    head_start_until: ay_core::time::Instant,
    /// Total wall budget the slice may consume.
    budget: Duration,
}

impl Solver {
    /// Gate and BUILD the bit-parallel support enumeration at
    /// startup-preprocessing entry, then park it: search runs first and the
    /// enumeration gets a metered slice afterwards
    /// (`search_with_parked_indep_enum`).
    ///
    /// The build has to happen here — BVE resolves away the Tseitin
    /// scaffolding the support is read from — but running here is what turned
    /// six fast SAT solves into timeouts (module docs).
    pub(super) fn prepare_indep_enum_at_startup(&mut self) {
        self.cold.indep_enum_pending = None;
        if !indep_enum_enabled() {
            return;
        }
        // Plain-CNF startup construction only (mirrors the GF-probe gate).
        // Scopes are excluded as well: a parked model is verified against the
        // original ledger, whose scoped clauses `verify_external_model` skips.
        if self.cold.ic3_mode
            || self.active_domain.is_some()
            || self.decision_domain.is_some()
            || self.decision_level != 0
            || !self.cold.scope_selectors.is_empty()
            || self.cold.has_ever_scoped
        {
            return;
        }
        let t0 = ay_core::time::Instant::now();
        let pending = self.indep_enum_park();
        self.stats.indep_enum_time_ns = self
            .stats
            .indep_enum_time_ns
            .saturating_add(t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64);
        self.cold.indep_enum_pending = pending.map(Box::new);
    }

    /// Wall budget for one enumeration slice, and the head start search gets
    /// before it: fractions of the budget the solver can actually see, or
    /// absolutes when the caller installed no deadline at all.
    fn indep_enum_schedule(&self) -> (Duration, Duration) {
        let visible = self
            .cold
            .solve_deadline
            .and_then(|deadline| deadline.checked_duration_since(ay_core::time::Instant::now()));
        match visible {
            Some(budget) => (
                budget
                    .mul_f64(INDEP_ENUM_HEAD_START_FRACTION)
                    .min(INDEP_ENUM_HEAD_START_MAX),
                budget
                    .mul_f64(INDEP_ENUM_BUDGET_FRACTION)
                    .min(INDEP_ENUM_BUDGET_MAX),
            ),
            None => (
                INDEP_ENUM_HEAD_START_NO_DEADLINE,
                INDEP_ENUM_BUDGET_NO_DEADLINE,
            ),
        }
    }

    /// Gate and build. `None` on any bail-out; the solver is untouched either
    /// way.
    fn indep_enum_park(&mut self) -> Option<PendingIndepEnum> {
        let program = self.indep_enum_admit()?;
        let EnumProgram {
            orig_of,
            kinds,
            starts,
            lits,
            support: dense_support,
        } = program;
        let ext_of: Vec<u32> = orig_of
            .iter()
            .map(|&v| self.cold.i2e.get(v as usize).copied().unwrap_or(v))
            .collect();
        let ext_len = self.cold.e2i.len().max(self.user_num_vars);
        let mut root_ext_model = vec![false; ext_len];
        for v in 0..self.num_vars {
            let ext = self.cold.i2e.get(v).copied().unwrap_or(v as u32) as usize;
            if ext < root_ext_model.len() {
                root_ext_model[ext] = self.vals[Literal::positive(Variable(v as u32)).index()] > 0;
            }
        }
        let (head_start, budget) = self.indep_enum_schedule();
        let engine = BitEnum::new(orig_of.len(), kinds, starts, lits, dense_support);
        tracing::info!(
            head_start_ms = head_start.as_millis() as u64,
            budget_ms = budget.as_millis() as u64,
            "indep enum: parked behind search's head start",
        );
        Some(PendingIndepEnum {
            engine,
            ext_of,
            root_ext_model,
            head_start_until: ay_core::time::Instant::now() + head_start,
            budget,
        })
    }

    /// The instant at which the parked enumeration is allowed to start, if one
    /// is parked at all.
    pub(super) fn indep_enum_head_start_until(&self) -> Option<ay_core::time::Instant> {
        self.cold
            .indep_enum_pending
            .as_ref()
            .map(|pending| pending.head_start_until)
    }

    /// Give the parked enumeration its metered slice.
    ///
    /// `Some(result)` only for a model verified against the original clause
    /// ledger. Every other outcome — budget exhausted, deadline, interrupt,
    /// exhaustion, stall, failed verification — returns `None` and leaves
    /// search to continue with the rest of the budget. UNSAT is never claimed
    /// (see the module docs).
    pub(super) fn run_parked_indep_enum(&mut self) -> Option<SatResult> {
        let mut pending = self.cold.indep_enum_pending.take()?;
        let t0 = ay_core::time::Instant::now();
        let slice_until = t0 + pending.budget;
        let outcome = {
            let engine = &mut pending.engine;
            let stop = || {
                self.is_interrupted()
                    || self.solve_deadline_expired()
                    || ay_core::time::Instant::now() >= slice_until
            };
            engine.run(&stop, INDEP_ENUM_MAX_VISITS)
        };
        let elapsed = t0.elapsed();
        self.stats.indep_enum_time_ns = self
            .stats
            .indep_enum_time_ns
            .saturating_add(elapsed.as_nanos().min(u128::from(u64::MAX)) as u64);
        self.stats.indep_enum_blocks = pending.engine.blocks;
        self.stats.indep_enum_visits = pending.engine.visits;
        self.stats.indep_enum_assignments = pending
            .engine
            .blocks
            .saturating_mul(pending.engine.columns_per_block());
        self.indep_enum_finish(&pending, outcome)
            .map(|model| self.declare_indep_enum_sat(model))
    }

    /// Interpret a slice outcome. `Some(external model)` only for a verified
    /// model.
    fn indep_enum_finish(
        &mut self,
        pending: &PendingIndepEnum,
        outcome: EnumOutcome,
    ) -> Option<Vec<bool>> {
        match outcome {
            EnumOutcome::Candidate { block, column } => {
                let model = self.indep_enum_external_model(pending, column);
                if !self.verify_external_model(&model) {
                    tracing::warn!(
                        block,
                        column,
                        "indep enum: surviving column failed original-formula verification; \
                         abandoning"
                    );
                    debug_assert!(false, "indep enum column failed self-verification");
                    self.stats.indep_enum_verify_failures += 1;
                    return None;
                }
                tracing::info!(
                    block,
                    column,
                    blocks = pending.engine.blocks,
                    visits = pending.engine.visits,
                    "indep enum: satisfying assignment found"
                );
                Some(model)
            }
            EnumOutcome::Exhausted => {
                // Would be UNSAT if the recovered definitions were exact and
                // the collapse were exact; neither is certified, and proof
                // mode would additionally owe a derivation. No verdict.
                self.stats.indep_enum_exhausted += 1;
                tracing::info!(
                    blocks = pending.engine.blocks,
                    "indep enum: support space exhausted with no model — falling through"
                );
                None
            }
            EnumOutcome::Stalled => {
                self.stats.indep_enum_stalled += 1;
                None
            }
            EnumOutcome::Stopped => {
                // The slice budget (or the whole-solve deadline / an
                // interrupt) ran out. The probe is done; search owns the rest
                // of the budget.
                self.stats.indep_enum_budget_exhausted += 1;
                tracing::info!(
                    blocks = pending.engine.blocks,
                    visits = pending.engine.visits,
                    "indep enum: slice budget spent with no model — search resumes"
                );
                None
            }
        }
    }

    /// Publish a verified enumeration model as the solve's SAT answer.
    ///
    /// The model is total over the ORIGINAL formula in external space, so it
    /// owes nothing to elimination reconstruction (which exists to lift a
    /// model of the SIMPLIFIED formula); it has already passed
    /// `verify_external_model`, the same authoritative original-ledger gate
    /// `finalize_sat_model` applies.
    fn declare_indep_enum_sat(&mut self, mut model: Vec<bool>) -> SatResult {
        self.tla_trace_step(CdclTraceState::Sat, Some(CdclTraceAction::DeclareSat));
        model.truncate(self.user_num_vars);
        self.emit_diagnostic_sat_summary(model.len());
        SatResult::Sat(model)
    }

    /// Gate, build, enumerate to completion, verify. `None` on any bail-out.
    ///
    /// The unmetered entry point: it runs the whole enumeration inline and is
    /// used by the module's tests. Production goes through
    /// `prepare_indep_enum_at_startup` + `run_parked_indep_enum`, which bound
    /// it by the solve budget.
    #[cfg(test)]
    fn indep_enum_probe(&mut self) -> Option<Vec<bool>> {
        let mut pending = self.indep_enum_park()?;
        let outcome = {
            let engine = &mut pending.engine;
            let stop = || self.is_interrupted() || self.solve_deadline_expired();
            engine.run(&stop, INDEP_ENUM_MAX_VISITS)
        };
        self.stats.indep_enum_blocks = pending.engine.blocks;
        self.stats.indep_enum_visits = pending.engine.visits;
        self.stats.indep_enum_assignments = pending
            .engine
            .blocks
            .saturating_mul(pending.engine.columns_per_block());
        self.indep_enum_finish(&pending, outcome)
    }

    /// Gate and build the program. `None` when the instance is not admitted.
    fn indep_enum_admit(&mut self) -> Option<EnumProgram> {
        // Cheap pre-gates: two comparisons for the whole rest of the corpus.
        let active = self.arena.active_clause_count();
        if self.num_vars == 0
            || self.num_vars > INDEP_ENUM_MAX_VARS
            || active == 0
            || active > INDEP_ENUM_MAX_CLAUSES
        {
            return None;
        }
        let support = self.compute_indep_support()?;
        if support.is_empty() || support.len() > INDEP_ENUM_MAX_SUPPORT {
            return None;
        }
        let program = self.build_enum_program(&support)?;
        let size = program.support.len();
        if size == 0 || size > INDEP_ENUM_MAX_SUPPORT {
            return None;
        }
        let blocks = 1u64 << (size as u32).saturating_sub(ENUM_BITS);
        let visits = blocks.saturating_mul(program.kinds.len() as u64);
        self.stats.indep_enum_support_size = size as u64;
        self.stats.indep_enum_constraints = program.kinds.len() as u64;
        self.stats.indep_enum_projected_visits = visits;
        if visits > INDEP_ENUM_MAX_VISITS {
            return None;
        }
        self.stats.indep_enum_admitted += 1;
        tracing::info!(
            support = size,
            constraints = program.kinds.len(),
            xors = program.kinds.iter().filter(|&&k| k == KIND_XOR).count(),
            blocks,
            "indep enum: admitted",
        );
        Some(program)
    }

    /// Reduce the active clause database to the engine's dense constraint set:
    /// drop root-satisfied clauses, drop root-false literals, compact the
    /// remaining variables, then collapse complete XOR parity classes.
    fn build_enum_program(&self, support: &[u32]) -> Option<EnumProgram> {
        let num_vars = self.num_vars;
        let mut dense_of = vec![u32::MAX; num_vars];
        let mut orig_of: Vec<u32> = Vec::new();
        // Reduced clauses as dense literal indices, in arena order (which for
        // a circuit CNF is close to evaluation order — a good initial queue).
        let mut raw: Vec<Vec<u32>> = Vec::new();
        let mut seen: Vec<u32> = vec![u32::MAX; num_vars * 2];
        let mut epoch = 0u32;
        for off in self.arena.indices() {
            if !self.arena.is_active(off) {
                continue;
            }
            let mut cur: Vec<u32> = Vec::new();
            let mut satisfied = false;
            let mut tautology = false;
            epoch = epoch.wrapping_add(1);
            for &lit in self.arena.literals(off) {
                let v = lit.variable().index();
                if v >= num_vars {
                    return None;
                }
                match self.vals[lit.index()] {
                    x if x > 0 => {
                        satisfied = true;
                        break;
                    }
                    x if x < 0 => continue,
                    _ => {}
                }
                let d = match dense_of[v] {
                    u32::MAX => {
                        let d = u32::try_from(orig_of.len()).ok()?;
                        dense_of[v] = d;
                        orig_of.push(v as u32);
                        d
                    }
                    d => d,
                };
                let dl = d * 2 + u32::from(!lit.is_positive());
                if seen[dl as usize] == epoch {
                    continue; // duplicate literal
                }
                if seen[(dl ^ 1) as usize] == epoch {
                    tautology = true;
                    break;
                }
                seen[dl as usize] = epoch;
                cur.push(dl);
            }
            if satisfied || tautology {
                continue;
            }
            if cur.is_empty() {
                // Root-falsified clause: the formula is already inconsistent
                // at level 0. Not this route's business.
                return None;
            }
            raw.push(cur);
        }
        if orig_of.len() > INDEP_ENUM_MAX_VARS {
            return None;
        }
        let dense_support: Vec<u32> = support
            .iter()
            .filter_map(|&v| match dense_of.get(v as usize) {
                Some(&d) if d != u32::MAX => Some(d),
                _ => None,
            })
            .collect();
        let (kinds, starts, lits) = collapse_xors(&raw);
        Some(EnumProgram {
            orig_of,
            kinds,
            starts,
            lits,
            support: dense_support,
        })
    }

    /// Read a surviving column out as a full assignment over the EXTERNAL
    /// variables: root-fixed variables keep the root value they had when the
    /// program was built, enumerated and propagated variables take their
    /// column bit, and a variable the block left unassigned (it occurs only in
    /// already-satisfied constraints) keeps its parked value.
    ///
    /// External space is what makes the parked slice safe: preprocessing
    /// renumbers INTERNAL variables between the park and the run, but external
    /// indices — the ones the original ledger is written in — never move.
    fn indep_enum_external_model(&self, pending: &PendingIndepEnum, column: usize) -> Vec<bool> {
        let mut model = pending.root_ext_model.clone();
        for (d, &ext) in pending.ext_of.iter().enumerate() {
            let Some(value) = pending.engine.column_value(d, column) else {
                continue;
            };
            if let Some(slot) = model.get_mut(ext as usize) {
                *slot = value;
            }
        }
        model
    }
}

/// Collapse complete XOR parity classes and emit the CSR constraint set.
///
/// A set of `2^(k-1)` distinct clauses over the same `k` variables, all with
/// the same parity of negated literals, is EXACTLY the CNF of one XOR
/// constraint (each clause forbids one assignment, and those are precisely the
/// `2^(k-1)` assignments of one parity). Replacing them is therefore
/// equivalence-preserving in both directions, and one XOR visit does the work
/// of `2^(k-1)` clause visits with the same propagation strength.
///
/// Emitted order follows the first clause each constraint came from, so the
/// circuit's evaluation order survives the collapse.
fn collapse_xors(raw: &[Vec<u32>]) -> (Vec<u8>, Vec<u32>, Vec<u32>) {
    let mut groups: HashMap<Vec<u32>, Vec<(usize, u32)>> = HashMap::new();
    for (i, c) in raw.iter().enumerate() {
        if c.len() < 2 || c.len() > INDEP_ENUM_XOR_MAX_ARITY {
            continue;
        }
        let mut vars: Vec<u32> = c.iter().map(|l| l >> 1).collect();
        vars.sort_unstable();
        // Sign mask relative to the sorted variable order.
        let mut mask = 0u32;
        for &l in c {
            let j = vars
                .binary_search(&(l >> 1))
                .expect("clause variable is in its own sorted variable list");
            mask |= (l & 1) << j;
        }
        groups.entry(vars).or_default().push((i, mask));
    }

    // (order key, kind, literals)
    let mut out: Vec<(usize, u8, Vec<u32>)> = Vec::with_capacity(raw.len());
    let mut consumed = vec![false; raw.len()];
    let mut keys: Vec<&Vec<u32>> = groups.keys().collect();
    // Deterministic emission independent of hash iteration order.
    keys.sort_unstable();
    for key in keys {
        let entries = &groups[key];
        let k = key.len();
        let need = 1usize << (k - 1);
        for parity in 0..2u32 {
            let members: Vec<(usize, u32)> = entries
                .iter()
                .copied()
                .filter(|&(_, m)| m.count_ones() % 2 == parity)
                .collect();
            let mut masks: Vec<u32> = members.iter().map(|&(_, m)| m).collect();
            masks.sort_unstable();
            masks.dedup();
            if masks.len() != need {
                continue;
            }
            let Some(order) = members.iter().map(|&(i, _)| i).min() else {
                continue;
            };
            // The clauses forbid every assignment of parity `parity`, so the
            // surviving constraint is `XOR(vars) = 1 ^ parity`. The engine
            // wants "an ODD number of literals is true": that is all-positive
            // when the required XOR value is 1, and one flipped literal when
            // it is 0.
            let mut xlits: Vec<u32> = key.iter().map(|v| v * 2).collect();
            if parity == 1 {
                xlits[0] |= 1;
            }
            for &(i, _) in &members {
                consumed[i] = true;
            }
            out.push((order, KIND_XOR, xlits));
        }
    }
    for (i, c) in raw.iter().enumerate() {
        if !consumed[i] {
            out.push((i, KIND_CLAUSE, c.clone()));
        }
    }
    out.sort_by_key(|entry| (entry.0, entry.1));

    let mut kinds = Vec::with_capacity(out.len());
    let mut starts = Vec::with_capacity(out.len() + 1);
    let mut lits: Vec<u32> = Vec::new();
    starts.push(0);
    for (_, kind, cl) in out {
        kinds.push(kind);
        lits.extend_from_slice(&cl);
        starts.push(lits.len() as u32);
    }
    (kinds, starts, lits)
}

#[cfg(test)]
mod tests;
