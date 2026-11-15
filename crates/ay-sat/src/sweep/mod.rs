// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT sweeping (equivalence merging) for CNF formulas.
//!
//! Two sweep modes:
//!
//! 1. **Kitten-based (default):** Builds a Cone-of-Influence (COI) for each
//!    active variable, feeds the clause neighborhood to the kitten sub-solver,
//!    and probes for backbone literals and literal equivalences. Finds
//!    equivalences from arbitrary clause neighborhoods, not just binary clauses.
//!    Reference: CaDiCaL `sweep.cpp` + `kitten.c`.
//!
//! 2. **SCC-based (fallback):** Detects equivalent literals in the binary-clause
//!    implication graph via 2-SAT SCC analysis. Only finds equivalences provable
//!    from binary clauses alone. Used when kitten sweep finds nothing new.
//!
//! 3. **Random simulation (#6868):** When COI probing finds no equivalences,
//!    random simulation assigns random values to variables, forward-propagates
//!    through clauses, and groups variables by simulation signatures. Candidate
//!    equivalence classes are then verified via kitten probing. Effective on
//!    uniform formulas where COI neighborhoods are uninformative.
//!
//! Split into submodules:
//! - `coi`: Cone-of-Influence construction for kitten sub-solver
//! - `probe`: Backbone and equivalence probing
//! - `rewrite`: Union-find lit_map construction and rewrite stats
//! - `simulation`: Random simulation-based candidate finding
//! - `env_kissat`, `probe_kissat`: Kissat 4.0.4's environment, sweep order
//!   and probing (`--sat-sweep-env-kissat`, default off)

mod counted;

use crate::clause_arena::ClauseArena;
use crate::kani_compat::DetHashSet as HashSet;
use crate::kitten::{CoreLemmas, Kitten, Terminator};
use crate::lit_marks::LitMarks;
use crate::literal::Literal;
use crate::occ_list::OccList;

mod coi;
mod env_kissat;
mod probe;
mod probe_kissat;
mod rewrite;
mod simulation;

#[cfg(test)]
mod env_kissat_tests;
#[cfg(test)]
mod limit_tests;
#[cfg(test)]
mod pass_tests;
#[cfg(test)]
mod tests;

/// Statistics for sweeping.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct SweepStats {
    /// Number of sweep rounds executed.
    pub rounds: u64,
    /// Number of binary clauses scanned for SCC implications.
    pub binary_clauses: u64,
    /// Number of SCC components found.
    pub components: u64,
    /// Number of variables proven contradictory.
    pub contradictions: u64,
    /// Number of literals rewritten via canonicalization.
    pub literals_rewritten: u64,
    /// Number of clauses changed (literals or length changed).
    pub clauses_rewritten: u64,
    /// Number of tautological clauses deleted after rewriting.
    pub clauses_deleted_tautology: u64,
    /// Number of clauses that became unit after rewriting.
    pub clauses_became_unit: u64,
    /// Number of clauses that became empty after rewriting.
    pub clauses_became_empty: u64,
    /// Number of kitten COI environments built.
    pub kitten_environments: u64,
    /// Number of backbone literals found by kitten.
    pub kitten_backbone: u64,
    /// Number of equivalences found by kitten.
    pub kitten_equivalences: u64,
    /// Number of signed partition refinements driven by SAT countermodels.
    pub kitten_partition_refinements: u64,
    /// Kitten solves and propagations spent by `sweep_with_kitten`.
    pub kitten_solves: u64,
    pub kitten_propagations: u64,
    /// Number of random simulation rounds executed.
    pub simulation_rounds: u64,
    /// Number of candidate equivalence classes found by simulation.
    pub simulation_candidates: u64,
    /// Sweep passes that reached the last candidate (`charge_all_work`, env-kissat).
    pub completed_passes: u64,
    /// COI environments kitten refuted outright (the formula is UNSAT).
    pub unsat_environments: u64,
    /// Sweep calls where rewriting under the equivalences produced the
    /// empty clause.
    pub unsat_rewrite_empty: u64,
    /// Sweep calls where a rewrite-derived unit contradicted the level-0
    /// assignment.
    pub unsat_contradicting_units: u64,
    /// UNSAT environments that could not be certified under a proof surface
    /// (no kitten core recorded) and were handed back to search instead.
    pub unsat_uncertified_fallbacks: u64,
    /// Sweep calls whose equivalences, each proved in its own environment,
    /// put a literal and its negation in one class: the formula is UNSAT.
    pub unsat_contradictory_equivalences: u64,
}

/// Outcome of a sweep round.
/// One sweep-derived fact together with the kitten core lemmas that certify
/// it, in the external literal encoding (`Literal.0` values). Lemmas are in
/// derivation order; each is RUP over the environment clauses plus the lemmas
/// before it, so a DRAT/VeriPB proof that adds them in order can then add the
/// fact as a RUP step (Kissat sweep.c save_core / add_core).
#[derive(Debug, Clone)]
pub(crate) enum SweepProofFact {
    /// `lit` is a backbone literal of the environment; `lemmas` certify
    /// `¬lit` UNSAT (empty when kitten had `lit` fixed at its root level,
    /// where the unit is RUP directly).
    Unit { lit: u32, lemmas: CoreLemmas },
    /// `lit ≡ rep`: `forward` certifies `lit ∧ ¬rep` UNSAT, i.e. the binary
    /// `(¬lit ∨ rep)`; `backward` certifies `¬lit ∧ rep` UNSAT, i.e. the
    /// binary `(lit ∨ ¬rep)`.
    Equivalence {
        rep: u32,
        lit: u32,
        forward: CoreLemmas,
        backward: CoreLemmas,
    },
    /// A whole COI environment is UNSAT (kitten answered 20 with no
    /// assumptions), so by monotonicity the formula is; `lemmas` certify
    /// it. Empty when kitten's root propagation alone refuted the
    /// environment, where the empty clause is RUP directly.
    Unsat { lemmas: CoreLemmas },
}

#[derive(Debug, Clone)]
pub(crate) struct SweepOutcome {
    /// If true, the formula is UNSAT (contradiction detected).
    pub(crate) unsat: bool,
    /// Canonical literal mapping for each literal index (size = 2*num_vars).
    pub(crate) lit_map: Vec<Literal>,
    /// Unit literals created by sweeping (backbone literals).
    pub(crate) new_units: Vec<Literal>,
    /// A literal the equivalences put in one class with its negation
    /// (`Literal.0` encoding): the formula is UNSAT, and `lit_map` is empty.
    /// Each equivalence was proved in its own COI environment, so all of them
    /// hold, and together they are contradictory; rewriting under the
    /// collapsed map would map both polarities of the class to one literal
    /// and leave a satisfiable residue (found by the 2026-09-17 audit as an
    /// UNSAT instance ending `unknown` under the VeriPB posture).
    pub(crate) contradiction: Option<u32>,
}

// COI construction limits (CaDiCaL defaults from sweep.cpp).
/// Per-COI-solve tick cap (see the #class-3 rationale at the use site).
/// Sweep-deepening default (B4: was AY_AB_SWEEP_DEEPEN; OFF is the measured
/// shipped behaviour, and flipping it belongs to a priced batch).
const SWEEP_DEEPEN_DEFAULT: bool = false;
/// Wall cap when deepening is on (B4: was AY_AB_SWEEP_WALL_MS).
#[allow(dead_code)]
const SWEEP_DEEPEN_WALL_LIMIT_MS: u64 = 1_000;
const SWEEP_PER_SOLVE_TICKS_CAP: u64 = 20_000;
const COI_VAR_LIMIT: usize = 48;
const COI_DEPTH_LIMIT: u32 = 4;
const COI_CLAUSE_LIMIT: usize = 4096;

/// Sweeping engine.
pub(crate) struct Sweeper {
    num_vars: usize,
    stats: SweepStats,
    marks: LitMarks,
    scratch: Vec<Literal>,
    // Kitten-based sweep data
    kitten: Kitten,
    // COI working buffers (reused across variables)
    coi_vars: Vec<usize>,
    coi_depths: Vec<u32>,
    coi_clauses: HashSet<usize>,
    // Sweep-deepening lever: persistent round-robin cursor
    // over the variable scan. Without deepening, each sweep call restarts at
    // variable 0, so on any formula larger than the per-call budget only the
    // low-index prefix is ever swept. With the cursor, successive calls resume
    // where the previous call's budget ran out, covering fresh variables.
    // kissat's `sweep_schedule` uses a persistent incomplete-set for the same
    // reason (sweep.c). Reset to 0 on compaction (Sweeper::new); resuming from
    // 0 after a compaction is harmless. Only read when the lever is enabled.
    sweep_cursor: usize,
    /// Collect certificate material (kitten core lemmas) for every derived
    /// fact of the current call. Set by the solver when a proof surface is
    /// active; it never changes what sweep decides, only what it records.
    want_proof: bool,
    /// Charge every part of an in-search sweep to its tick budget, not only
    /// kitten's propagation: the environments built (one tick per clause fed;
    /// 14,000 environments per sweep on schooltt-5-3 with 1 yield, about a
    /// second each while kitten's own ticks stayed under the budget) and the
    /// candidate simulation (`find_candidates_by_simulation_budgeted`).
    charge_all_work: bool,
    /// The sweep pass each variable was last swept in, and the current pass:
    /// under `charge_all_work` a variable is skipped until the pass over all
    /// candidates completes (Kissat's `swept` flags and `sweep_completed`),
    /// instead of being solved again on every sweep from variable 0 (585K
    /// environments for one yield on schooltt-5-3, the sweep's whole 10
    /// percent budget spent on the same variables each time).
    swept_in_pass: Vec<u32>,
    sweep_pass: u32,
    proof_facts: Vec<SweepProofFact>,
    /// `--sat-sweep-env-kissat`: Kissat 4.0.4's growing environment, sweep
    /// order and probing (`env_kissat.rs`, `probe_kissat.rs`).
    env_kissat: bool,
    /// Under `env_kissat`: the backbones and equivalences the current call
    /// has proved so far.
    kissat_call: env_kissat::KissatCall,
    /// The owning solver's `--sat-deterministic-inproc`: the wall cap is off
    /// and the tick budget alone bounds a call (`set_deterministic`).
    deterministic: bool,
    /// The current call's tick budget, checked before every environment and
    /// every probe (`limit_hit`).
    call: CallBudget,
}

/// One sweep call's tick budget: kitten's ticks since `start`, plus the work
/// charged outside kitten (`charge_all_work`).
#[derive(Clone, Copy)]
struct CallBudget {
    start: u64,
    budget: u64,
    outside_kitten: u64,
}

impl CallBudget {
    /// Before the first call, probes run by hand (tests) spend against no
    /// budget.
    const UNLIMITED: Self = Self {
        start: 0,
        budget: u64::MAX,
        outside_kitten: 0,
    };
}

impl Sweeper {
    #[inline]
    fn randomized_kitten_solve(&mut self) -> i32 {
        self.kitten.randomize_phases();
        self.kitten.solve()
    }

    /// Create a new sweeper for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            stats: SweepStats::default(),
            marks: LitMarks::new(num_vars),
            scratch: Vec::new(),
            kitten: {
                // Antecedent tracking is on in BOTH postures so the kitten
                // search is identical with and without a proof surface
                // (proof-posture-parity); cores are only extracted when
                // `want_proof` is set.
                let mut kitten = Kitten::new();
                kitten.enable_antecedent_tracking();
                kitten
            },
            coi_vars: Vec::new(),
            coi_depths: vec![0; num_vars],
            coi_clauses: HashSet::default(),
            sweep_cursor: 0,
            want_proof: false,
            charge_all_work: false,
            swept_in_pass: vec![0; num_vars],
            sweep_pass: 1,
            proof_facts: Vec::new(),
            env_kissat: false,
            kissat_call: env_kissat::KissatCall::default(),
            deterministic: crate::determinism::deterministic_inproc_enabled(),
            call: CallBudget::UNLIMITED,
        }
    }

    /// What ends the next sweeps early besides their tick budget: the owning
    /// solver's interrupt flag and deadline. Every kitten solve polls it while
    /// it propagates, and the sweep polls it before every environment and
    /// every probe.
    pub(crate) fn set_terminator(&mut self, terminator: Terminator) {
        self.kitten.set_terminator(terminator);
    }

    /// Ticks the current call has spent: kitten's, plus the work charged
    /// outside it.
    fn call_ticks_spent(&self) -> u64 {
        self.kitten
            .current_ticks()
            .saturating_sub(self.call.start)
            .saturating_add(self.call.outside_kitten)
    }

    /// CaDiCaL's `terminated_asynchronously () || kitten_ticks_limit_hit ()`
    /// (sweep.cpp:197-208), checked before every environment and every probe:
    /// the solver asked to stop, or the call's budget is spent. A kitten solve
    /// stops at its tick limit only at its next free decision, after it has
    /// propagated its environment and assumptions again, so without this check
    /// the probes of an environment went on past the budget at that cost each.
    fn limit_hit(&mut self) -> bool {
        self.kitten.terminated() || self.call_ticks_spent() >= self.call.budget
    }

    /// Whether the next `sweep_with_kitten` call records certificate material.
    pub(crate) fn set_proof_facts_wanted(&mut self, wanted: bool) {
        self.want_proof = wanted;
    }

    /// Whether the next sweep charges its environment building and candidate
    /// simulation to the tick budget (in-search sweeps under
    /// `--sat-inproc-nlogn-schedule true`).
    pub(crate) fn set_charge_all_work(&mut self, charge: bool) {
        self.charge_all_work = charge;
    }

    /// Whether the next sweep uses Kissat 4.0.4's environment, sweep order
    /// and probing (`--sat-sweep-env-kissat`).
    pub(crate) fn set_env_kissat(&mut self, on: bool) {
        self.env_kissat = on;
    }

    /// Whether the next sweep runs on counted work only, the owning solver's
    /// `--sat-deterministic-inproc` (`Solver::set_deterministic_inproc`).
    pub(crate) fn set_deterministic(&mut self, on: bool) {
        self.deterministic = on;
    }

    /// Drain the certificate material recorded by the last call.
    pub(crate) fn take_proof_facts(&mut self) -> Vec<SweepProofFact> {
        std::mem::take(&mut self.proof_facts)
    }

    /// Kitten refuted the current COI environment with no assumptions. Count
    /// it and, under a proof surface, keep the core lemmas that certify the
    /// refutation — taken now, before `clear_coi` resets kitten.
    fn record_environment_unsat(&mut self) {
        self.stats.unsat_environments += 1;
        if self.want_proof {
            let lemmas = self.kitten.core_lemmas_external();
            self.proof_facts.push(SweepProofFact::Unsat { lemmas });
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        self.marks.ensure_num_vars(num_vars);
        self.coi_depths.resize(num_vars, 0);
    }

    /// Get sweep statistics.
    pub(crate) fn stats_mut(&mut self) -> &mut SweepStats {
        &mut self.stats
    }

    pub(crate) fn stats(&self) -> &SweepStats {
        &self.stats
    }

    /// Restore previously saved statistics after compaction recreates the engine.
    pub(crate) fn restore_stats(&mut self, stats: SweepStats) {
        self.stats = stats;
    }

    /// The pass marks and the pass they belong to, taken for an arena
    /// compaction: `compact.rs` re-creates the engine, and without this the
    /// marks reset with it — 498 compactions in one schooltt-5-3 run, so
    /// every sweep started over at variable 0 and the passes never advanced.
    pub(crate) fn take_pass_state(&mut self) -> (Vec<u32>, u32) {
        (std::mem::take(&mut self.swept_in_pass), self.sweep_pass)
    }

    /// Restore the marks taken by `take_pass_state`, already remapped to the
    /// compacted variable indices; a missing entry is an unswept variable.
    pub(crate) fn restore_pass_state(&mut self, mut marks: Vec<u32>, pass: u32) {
        marks.resize(self.num_vars, 0);
        self.swept_in_pass = marks;
        self.sweep_pass = pass.max(1);
    }

    // ── Kitten-based sweep ──────────────────────────────────────────

    /// `sweep_with_kitten`, adding the kitten solves and propagations it
    /// spends to the stats.
    pub(crate) fn sweep_counting_kitten_work(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        ticks_budget: u64,
    ) -> SweepOutcome {
        let (solves, propagations) = self.kitten.lifetime_work();
        let outcome = self.sweep_with_kitten(clauses, vals, frozen, ticks_budget);
        let (solves_after, propagations_after) = self.kitten.lifetime_work();
        self.stats.kitten_solves += solves_after.saturating_sub(solves);
        self.stats.kitten_propagations += propagations_after.saturating_sub(propagations);
        outcome
    }

    /// Run kitten-based sweep: COI construction + backbone/equivalence probing.
    ///
    /// For each active variable, builds a clause neighborhood (COI), feeds it
    /// to the kitten sub-solver, and probes for backbone literals and literal
    /// equivalences via flip + SAT-based probing.
    ///
    /// Reference: CaDiCaL sweep.cpp lines 1517-1710.
    pub(crate) fn sweep_with_kitten(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        ticks_budget: u64,
    ) -> SweepOutcome {
        self.stats.rounds += 1;
        self.proof_facts.clear();
        // `--sat-sweep-env-kissat`: this call's environment limits, fixed at
        // its start from the passes completed so far (Kissat's
        // `init_sweeper`, sweep.c:107-137, before `schedule_sweeping`).
        let env = self
            .env_kissat
            .then(|| env_kissat::EnvLimits::kissat(self.stats.completed_passes));
        if env.is_some() {
            self.kissat_call.begin_call();
            // Variables added since the engine was built (factoring's and
            // SBVA's extension variables, `ensure_num_vars`) need pass marks
            // too, or every call of the pass sweeps them again.
            self.swept_in_pass.resize(self.num_vars, 0);
        }
        // Pass marks: under `charge_all_work`, and always under Kissat's
        // environment, which grows with every completed pass.
        let track_passes = self.charge_all_work || env.is_some();

        let num_lits = self.num_vars * 2;
        // Build temporary occurrence lists for COI construction. Sweep only
        // reads them (`get`, `count`), so no position maps: on 2c458ef3's
        // 35.6M-clause arena their HashMap inserts cost 50-70 s per build.
        let mut occ = OccList::new_occ_only(self.num_vars);
        for idx in clauses.indices() {
            if clauses.is_dead(idx) {
                continue;
            }
            // Kissat's dense occurrence lists hold binaries and irredundant
            // clauses only (sweep.c:104-105): no environment takes a learned
            // clause longer than two, and the sweep order counts without them.
            if env.is_some() && clauses.is_learned(idx) && clauses.len_of(idx) > 2 {
                continue;
            }
            occ.add_clause(idx, clauses.literals(idx));
        }

        // Track equivalences: (lit_a, lit_b) meaning a ≡ b.
        let mut equivalences: Vec<(u32, u32)> = Vec::new();
        let mut new_units: Vec<Literal> = Vec::new();
        let mut unsat = false;

        self.call = CallBudget {
            start: self.kitten.current_ticks(),
            budget: ticks_budget,
            outside_kitten: 0,
        };
        // Wall-clock limit per sweep call (#8448): on small formulas, tick
        // budgets can be exhausted slowly while consuming significant wall
        // time (e.g., stable-300: ~570ms per round with only 3K ticks).
        // Cap each sweep call at 200ms to match backbone's wall limit.
        let sweep_wall_start = ay_core::time::Instant::now();
        const SWEEP_WALL_LIMIT_MS_DEFAULT: u64 = 200;
        // Deterministic inprocessing (#det wf_6503d3eb): when enabled, drop the
        // wall-clock cap entirely and rely on the deterministic kitten
        // `ticks_budget` (derived from the search_ticks delta) plus the
        // `0..n_vars` loop bound — both machine-independent — so sweep coverage
        // no longer depends on host load. The wall cap only ever *shortened*
        // sweep on small formulas where ticks accrue slowly; the tick budget
        // and variable bound keep it bounded without it.
        let det_inproc = self.deterministic;
        // Kissat has no wall cap. Under its environment an in-search sweep
        // charges every part of its work to the tick budget
        // (`charge_all_work`), which bounds it instead; the first sweep keeps
        // the cap.
        let wall_capped = !det_inproc && (env.is_none() || !self.charge_all_work);

        // ── Sweep-deepening lever (B4: env reads deleted; constant default) ──
        // OFF (default): restart the scan at variable 0 with the historical
        //   200ms wall cap — byte-for-byte the previous behaviour.
        // ON: resume the scan from a persistent round-robin cursor and relax
        //   the wall cap (default 1000ms) so successive
        //   calls advance coverage into fresh variables instead of re-probing
        //   the same low-index prefix every time. Matches kissat's persistent
        //   `sweep_schedule` (sweep.c).
        // B4: the AY_AB_SWEEP_{DEEPEN,WALL_MS} env reads are deleted. The
        // machinery is kept: deepening is a real capability (kissat's
        // persistent sweep_schedule) whose default decision belongs to the
        // measured batch that prices it, via a typed option -- not to an env
        // var nothing sets. Shipped behaviour is unchanged (OFF).
        let deepen = SWEEP_DEEPEN_DEFAULT;
        let sweep_wall_limit_ms = if deepen {
            SWEEP_DEEPEN_WALL_LIMIT_MS
        } else {
            SWEEP_WALL_LIMIT_MS_DEFAULT
        };
        let n_vars = self.num_vars;
        let scan_start = if deepen && n_vars > 0 {
            self.sweep_cursor % n_vars
        } else {
            0
        };

        // Kissat's sweep order: fewest occurrences first (sweep.c:1478-1529).
        let order = env.map(|limits| self.kissat_schedule(&occ, vals, frozen, limits));
        let n_steps = order.as_ref().map_or(n_vars, Vec::len);

        // Set when a budget cuts the pass before the last candidate.
        let mut pass_cut = false;
        for step in 0..n_steps {
            // Rotating index: OFF path visits 0..n exactly (var_idx == step);
            // ON path visits scan_start..n then 0..scan_start (round-robin).
            let var_idx = if let Some(order) = &order {
                order[step]
            } else {
                let v = scan_start + step;
                if v >= n_vars {
                    v - n_vars
                } else {
                    v
                }
            };
            // Skip assigned, frozen, or eliminated variables.
            let pos_idx = var_idx * 2;
            let neg_idx = var_idx * 2 + 1;
            if pos_idx >= vals.len() || vals[pos_idx] != 0 {
                continue;
            }
            if var_idx < frozen.len() && frozen[var_idx] > 0 {
                continue;
            }
            // Skip variables with no clauses.
            if occ.count(Literal(pos_idx as u32)) == 0 && occ.count(Literal(neg_idx as u32)) == 0 {
                continue;
            }
            // Swept in this pass already (Kissat's `swept`).
            if track_passes && self.swept_in_pass.get(var_idx) == Some(&self.sweep_pass) {
                continue;
            }
            // Proved a backbone earlier in this call (Kissat assigns the unit
            // at once and skips inactive variables, sweep.c:1273-1274).
            if env.is_some() && self.kissat_call.is_fixed(var_idx) {
                continue;
            }

            // Check tick budget (CaDiCaL sweep.cpp:1673) and the stop.
            let elapsed_ticks = self.call_ticks_spent();
            if elapsed_ticks >= ticks_budget || self.kitten.terminated() {
                // Deepening: resume at this unprobed variable next call.
                self.sweep_cursor = var_idx;
                pass_cut = true;
                break;
            }

            // Wall-clock limit (#8448): break if sweep has exceeded its
            // per-call wall-clock budget. Checked every 16 variables to
            // amortize the syscall cost of Instant::now(). Skipped entirely in
            // deterministic mode (#det wf_6503d3eb) — the kitten tick budget and
            // variable bound provide a machine-independent stop instead.
            // Kissat's order visits indices out of turn: count steps there.
            let wall_step = if order.is_some() { step } else { var_idx };
            if wall_capped
                && wall_step & 0xF == 0
                && sweep_wall_start.elapsed().as_millis() as u64 >= sweep_wall_limit_ms
            {
                // Deepening: resume at this unprobed variable next call.
                self.sweep_cursor = var_idx;
                pass_cut = true;
                break;
            }

            // Set remaining ticks as kitten's per-solve limit (CaDiCaL
            // set_kitten_ticks_limit pattern). Without this, a single
            // variable's COI probing can exhaust the entire sweep budget.
            // On shuffling-2 (138K vars, 4.7M clauses), the first
            // variable's probing consumed 138M ticks, preventing sweep
            // from reaching any other variables (#8448).
            let remaining = ticks_budget - elapsed_ticks;
            // Per-solve cap (#class-3, "cheaper coverage" principle): giving
            // each COI-solve the WHOLE remaining budget lets one hard COI
            // starve the rest (few vars covered). Cap per-solve so hard COIs
            // fail fast and more variables get probed.
            // B4: the AY_AB_SWEEP_PERSOLVE override is deleted -- it was an
            // uncached getenv PER SWEPT VARIABLE on the hot path (#8506).
            // Kissat has no per-environment cap (sweep.c:53-60, 196): every
            // environment may spend the call's whole remaining budget.
            let per_solve_cap = if env.is_some() {
                u64::MAX
            } else {
                SWEEP_PER_SOLVE_TICKS_CAP
            };
            self.kitten.set_ticks_limit(remaining.min(per_solve_cap));

            // Build COI environment for this variable.
            let clauses_fed = match env {
                Some(limits) => self.build_coi_kissat(var_idx, clauses, &occ, vals, limits),
                None => self.build_coi(var_idx, clauses, &occ, vals),
            };
            if self.charge_all_work {
                self.call.outside_kitten += clauses_fed as u64;
            }
            if let Some(slot) = self.swept_in_pass.get_mut(var_idx) {
                *slot = self.sweep_pass;
            }
            if clauses_fed == 0 {
                self.clear_coi();
                continue;
            }
            self.kitten.seal_original();
            self.stats.kitten_environments += 1;

            // Initial solve on the COI.
            let result = self.randomized_kitten_solve();
            if result == 20 {
                // UNSAT neighborhood → the main formula is UNSAT.
                unsat = true;
                self.record_environment_unsat();
                self.clear_coi();
                break;
            }
            if result != 10 {
                // Timeout or unknown — kitten may have hit ticks limit.
                self.clear_coi();
                continue;
            }

            // SAT: probe backbone literals and equivalences using incremental kitten.
            if env.is_some() {
                self.probe_kissat(clauses, vals, frozen, &mut new_units, &mut equivalences);
            } else {
                self.probe_backbone_and_equivalences(
                    clauses,
                    vals,
                    frozen,
                    &mut new_units,
                    &mut equivalences,
                );
            }

            self.clear_coi();
        }
        if track_passes && !unsat && !pass_cut {
            // Every candidate was swept in this pass: the next sweep starts a
            // new pass over all of them (Kissat's `sweep_completed`).
            self.sweep_pass = self.sweep_pass.wrapping_add(1).max(1);
            self.stats.completed_passes += 1;
        }

        if unsat {
            return SweepOutcome {
                unsat: true,
                lit_map: Vec::new(),
                new_units,
                contradiction: None,
            };
        }

        // After the kitten flush_trail fix (#7049), COI probing is sound:
        // each incremental probe starts with clean trail/values, matching
        // CaDiCaL kitten.c:1433-1439 flush_trail(). No full-formula
        // verification needed. CaDiCaL sweep.cpp:1456-1515 trusts kitten
        // results directly. debug_assert in probe_partition_classes catches
        // any regression in debug builds.

        // Random simulation fallback (#6868): when COI probing found no
        // equivalences, run random simulation to discover candidates that
        // COI may have missed (e.g., on uniform formulas with no binary
        // clauses where COI neighborhoods are uninformative).
        if equivalences.is_empty()
            && self.kitten.current_ticks().saturating_sub(self.call.start) < ticks_budget
            && !self.kitten.terminated()
        {
            let sim_budget = self
                .charge_all_work
                .then(|| ticks_budget.saturating_sub(self.call_ticks_spent()));
            let (sim_classes, sim_rounds, sim_ticks) =
                self.find_candidates_by_simulation_budgeted(clauses, vals, frozen, sim_budget);
            self.stats.simulation_rounds += sim_rounds;
            self.stats.simulation_candidates += sim_classes.len() as u64;
            if self.charge_all_work {
                self.call.outside_kitten += sim_ticks;
            }

            // Verify simulation candidates with kitten: for each class, build
            // a combined COI environment and run partition probing.
            for class in &sim_classes {
                if class.len() < 2 {
                    continue;
                }
                if self.limit_hit() {
                    break;
                }

                // Build a COI environment covering all variables in this class.
                // Use the first variable as the seed, expanding to include
                // clauses containing other class members.
                let seed_var = (class[0] >> 1) as usize;
                let mut clauses_fed = self.build_coi(seed_var, clauses, &occ, vals);
                if clauses_fed == 0 {
                    self.clear_coi();
                    continue;
                }

                // Add clauses for other class members that weren't reached by COI BFS.
                for &signed_lit in class.iter().skip(1) {
                    let var = (signed_lit >> 1) as usize;
                    if var < self.coi_depths.len() && self.coi_depths[var] == 0 {
                        // Track this variable for cleanup by clear_coi().
                        self.coi_depths[var] = 1;
                        self.coi_vars.push(var);

                        // Variable not in COI; add its clauses directly.
                        for sign in 0..2u32 {
                            let lit = Literal(var as u32 * 2 + sign);
                            for &clause_idx in occ.get(lit) {
                                if self.coi_clauses.contains(&clause_idx) {
                                    continue;
                                }
                                if clauses.is_dead(clause_idx) {
                                    continue;
                                }
                                if clauses.is_learned(clause_idx) && clauses.len_of(clause_idx) > 2
                                {
                                    continue;
                                }
                                self.coi_clauses.insert(clause_idx);
                                let cls_lits = clauses.literals(clause_idx);
                                let mut ext_lits: Vec<u32> = Vec::new();
                                let mut sat = false;
                                for &l in cls_lits {
                                    let li = l.index();
                                    if li < vals.len() {
                                        if vals[li] > 0 {
                                            sat = true;
                                            break;
                                        }
                                        if vals[li] < 0 {
                                            continue;
                                        }
                                    }
                                    ext_lits.push(l.0);
                                }
                                if !sat {
                                    self.kitten.add_clause_with_id(
                                        clause_idx as u32,
                                        &ext_lits,
                                        u32::MAX,
                                    );
                                    clauses_fed += 1;
                                }
                            }
                        }
                    }
                }

                self.kitten.seal_original();
                self.stats.kitten_environments += 1;
                // Under `charge_all_work` the environment is charged like the
                // ones the variable loop builds, its class members' clauses
                // included.
                if self.charge_all_work {
                    self.call.outside_kitten += clauses_fed as u64;
                }

                // Fresh per-solve tick budget. set_ticks_limit is RELATIVE to
                // kitten's cumulative (never-reset) tick counter; the per-var
                // loop above set it against a much earlier tick count, so
                // without refreshing it here every simulation-verify solve
                // inherits an already-expired limit and returns instantly with
                // no result — silently disabling the whole simulation fallback.
                let sim_remaining = ticks_budget.saturating_sub(self.call_ticks_spent());
                self.kitten.set_ticks_limit(sim_remaining);

                // Solve the combined environment.
                let result = self.randomized_kitten_solve();
                if result == 20 {
                    unsat = true;
                    self.record_environment_unsat();
                    self.clear_coi();
                    break;
                }
                if result == 10 {
                    // Probe the simulation class for equivalences.
                    self.probe_partition_classes(clauses, vals, class, &mut equivalences);
                }

                self.clear_coi();
            }
        }

        if unsat {
            return SweepOutcome {
                unsat: true,
                lit_map: Vec::new(),
                new_units,
                contradiction: None,
            };
        }

        let (lit_map, contradiction) =
            self.build_lit_map_from_equivalences(&equivalences, frozen, num_lits);
        if contradiction.is_some() {
            self.stats.unsat_contradictory_equivalences += 1;
        }

        // Count rewriting stats (non-destructive scan).
        if !lit_map.is_empty() {
            self.count_rewrite_stats(clauses, &lit_map);
        }

        SweepOutcome {
            unsat: false,
            lit_map,
            new_units,
            contradiction,
        }
    }
}
