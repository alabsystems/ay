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

use crate::clause_arena::ClauseArena;
use crate::kani_compat::DetHashSet as HashSet;
use crate::kitten::Kitten;
use crate::lit_marks::LitMarks;
use crate::literal::Literal;
use crate::occ_list::OccList;

mod coi;
mod probe;
mod rewrite;
mod simulation;

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
    /// Number of random simulation rounds executed.
    pub simulation_rounds: u64,
    /// Number of candidate equivalence classes found by simulation.
    pub simulation_candidates: u64,
}

/// Outcome of a sweep round.
#[derive(Debug, Clone)]
pub(crate) struct SweepOutcome {
    /// If true, the formula is UNSAT (contradiction detected).
    pub(crate) unsat: bool,
    /// Canonical literal mapping for each literal index (size = 2*num_vars).
    pub(crate) lit_map: Vec<Literal>,
    /// Unit literals created by sweeping (backbone literals).
    pub(crate) new_units: Vec<Literal>,
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
            kitten: Kitten::new(),
            coi_vars: Vec::new(),
            coi_depths: vec![0; num_vars],
            coi_clauses: HashSet::default(),
            sweep_cursor: 0,
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
    pub(crate) fn stats(&self) -> &SweepStats {
        &self.stats
    }

    /// Restore previously saved statistics after compaction recreates the engine.
    pub(crate) fn restore_stats(&mut self, stats: SweepStats) {
        self.stats = stats;
    }

    // ── Kitten-based sweep ──────────────────────────────────────────

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

        let num_lits = self.num_vars * 2;
        // Build temporary occurrence lists for COI construction.
        let mut occ = OccList::new(self.num_vars);
        for idx in clauses.indices() {
            if clauses.is_garbage(idx) || clauses.is_empty_clause(idx) {
                continue;
            }
            occ.add_clause(idx, clauses.literals(idx));
        }

        // Track equivalences: (lit_a, lit_b) meaning a ≡ b.
        let mut equivalences: Vec<(u32, u32)> = Vec::new();
        let mut new_units: Vec<Literal> = Vec::new();
        let mut unsat = false;

        let start_ticks = self.kitten.current_ticks();
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
        let det_inproc = crate::determinism::deterministic_inproc_enabled();

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

        for step in 0..n_vars {
            // Rotating index: OFF path visits 0..n exactly (var_idx == step);
            // ON path visits scan_start..n then 0..scan_start (round-robin).
            let var_idx = {
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

            // Check tick budget (CaDiCaL sweep.cpp:1673).
            let elapsed_ticks = self.kitten.current_ticks().saturating_sub(start_ticks);
            if elapsed_ticks >= ticks_budget {
                // Deepening: resume at this unprobed variable next call.
                self.sweep_cursor = var_idx;
                break;
            }

            // Wall-clock limit (#8448): break if sweep has exceeded its
            // per-call wall-clock budget. Checked every 16 variables to
            // amortize the syscall cost of Instant::now(). Skipped entirely in
            // deterministic mode (#det wf_6503d3eb) — the kitten tick budget and
            // variable bound provide a machine-independent stop instead.
            if !det_inproc
                && var_idx & 0xF == 0
                && sweep_wall_start.elapsed().as_millis() as u64 >= sweep_wall_limit_ms
            {
                // Deepening: resume at this unprobed variable next call.
                self.sweep_cursor = var_idx;
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
            let per_solve_cap = SWEEP_PER_SOLVE_TICKS_CAP;
            self.kitten.set_ticks_limit(remaining.min(per_solve_cap));

            // Build COI environment for this variable.
            let clauses_fed = self.build_coi(var_idx, clauses, &occ, vals);
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
                self.clear_coi();
                break;
            }
            if result != 10 {
                // Timeout or unknown — kitten may have hit ticks limit.
                self.clear_coi();
                continue;
            }

            // SAT: probe backbone literals and equivalences using incremental kitten.
            self.probe_backbone_and_equivalences(
                clauses,
                vals,
                frozen,
                &mut new_units,
                &mut equivalences,
            );

            self.clear_coi();
        }

        if unsat {
            return SweepOutcome {
                unsat: true,
                lit_map: Vec::new(),
                new_units,
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
            && self.kitten.current_ticks().saturating_sub(start_ticks) < ticks_budget
        {
            let sim_classes = self.find_candidates_by_simulation(clauses, vals, frozen);
            self.stats.simulation_rounds += 64;
            self.stats.simulation_candidates += sim_classes.len() as u64;

            // Verify simulation candidates with kitten: for each class, build
            // a combined COI environment and run partition probing.
            for class in &sim_classes {
                if class.len() < 2 {
                    continue;
                }
                if self.kitten.current_ticks().saturating_sub(start_ticks) >= ticks_budget {
                    break;
                }

                // Build a COI environment covering all variables in this class.
                // Use the first variable as the seed, expanding to include
                // clauses containing other class members.
                let seed_var = (class[0] >> 1) as usize;
                let clauses_fed = self.build_coi(seed_var, clauses, &occ, vals);
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
                                if clauses.is_garbage(clause_idx)
                                    || clauses.is_empty_clause(clause_idx)
                                {
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
                                }
                            }
                        }
                    }
                }

                self.kitten.seal_original();
                self.stats.kitten_environments += 1;

                // Fresh per-solve tick budget. set_ticks_limit is RELATIVE to
                // kitten's cumulative (never-reset) tick counter; the per-var
                // loop above set it against a much earlier tick count, so
                // without refreshing it here every simulation-verify solve
                // inherits an already-expired limit and returns instantly with
                // no result — silently disabling the whole simulation fallback.
                let sim_elapsed = self.kitten.current_ticks().saturating_sub(start_ticks);
                let sim_remaining = ticks_budget.saturating_sub(sim_elapsed);
                self.kitten.set_ticks_limit(sim_remaining);

                // Solve the combined environment.
                let result = self.randomized_kitten_solve();
                if result == 20 {
                    unsat = true;
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
            };
        }

        let lit_map = self.build_lit_map_from_equivalences(&equivalences, frozen, num_lits);

        // Count rewriting stats (non-destructive scan).
        if !lit_map.is_empty() {
            self.count_rewrite_stats(clauses, &lit_map);
        }

        SweepOutcome {
            unsat: false,
            lit_map,
            new_units,
        }
    }
}

#[cfg(test)]
mod hot_path_env_tests {
    /// B4: the sweep hot path must contain zero environment reads. Before
    /// this batch, AY_AB_SWEEP_PERSOLVE was an uncached getenv + String alloc
    /// + parse PER SWEPT VARIABLE, and AY_AB_COI_{VARS,DEPTH} were read per
    /// variable inside build_coi -- all three violating the #8506
    /// no-per-call-syscall convention this module itself cites. This is the
    /// property that regresses, so it is the property under test.
    #[test]
    fn no_env_read_on_the_sweep_hot_path() {
        // Needle built by concatenation so this test's own source cannot
        // satisfy it (include_str! sees this file, comments included).
        let needle = concat!("env", "::", "var");
        for src in [include_str!("mod.rs"), include_str!("coi.rs")] {
            assert!(
                !src.contains(needle),
                "sweep hot path must not read the environment"
            );
        }
    }
}
