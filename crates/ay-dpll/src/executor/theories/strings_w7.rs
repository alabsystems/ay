// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! W7 — chain-definition, multi-atom and witness-enumerating witness moves
//! (default ON, `AY_STR_W7=0` kill switch).
//!
//! ## The measured gap W7 closes
//!
//! After W4 ([`super::strings_w4`], per-position climb), W5
//! ([`super::strings_w5`], single-needle placement search) and W6
//! ([`super::strings_w6`], digit/regex-word moves), the sat-side residue on the
//! 600-file QF_S + QF_SLIA canary is 11 files in exactly three shapes, and the
//! W6 report characterised each precisely:
//!
//! * **(A) 3 × `lib_int-ipaddress/ip_int_from_string`.** `ip_str` is split into
//!   `_EXTEND_VAR_0 … _EXTEND_VAR_7` by a chain of
//!   `(= _EXTEND_VAR_i (str.substr … (str.indexof … ":" …) …))` DEFINITIONS, and
//!   the per-position constraints are all written about the DEFINED variables
//!   (`(str.contains "0123456789ABCDEF…" (str.at _EXTEND_VAR_0 0))`,
//!   `(< 0 (str.len _EXTEND_VAR_3))`). W5 can search where the `":"` separators
//!   land and W6 can propose digit texts, but neither can do both jointly:
//!   [`Executor::w4_origin`] stops at the defined VARIABLE, so no atom about
//!   `_EXTEND_VAR_i` ever names a position of `ip_str`, and every edit W4/W5/W6
//!   make to a defined variable is contradicted by that variable's own defining
//!   equation.
//! * **(B) 7 × wide plateau** (4 kaluza, 1 Kepler, 1 Leetcode, 1
//!   `leetcode_int-numDecodings`). More than one atom is violated at the
//!   plateau, so W5's placement loop — which requires a SINGLE placement to
//!   strictly improve — cannot search it. W6 already refuted the cheap
//!   alternative: widening W4's sideways tolerance 2 → 5 converted nothing and
//!   let the climb leave W5's basin.
//! * **(C) 1 × stringfuzz `regex-026`.** `x, y ∈ (BB(##)*)*`, `x ≠ y`,
//!   `len x = len y`: the witness needs TWO DISTINCT WORDS of the same language
//!   at the same length. `find_witness_bounded` is a witness FINDER — it returns
//!   one word — so every candidate assigns `x` and `y` the same value and is
//!   refuted by the disequality.
//!
//! ## What W7 adds
//!
//! One pre-pass, [`Executor::try_w7_witnesses`], running LAST in the cascade
//! (after W6's regex-word pass) with its own budget. Ordering is not cosmetic:
//! W6 measured that running its moves BEFORE W5 cost 24 of W5's conversions by
//! displacing candidates on ties and exhausting budgets, so W7 is appended, and
//! only formulas nothing earlier decides ever reach it.
//!
//! 1. **Chain-definition search (shape A + most of B).** Harvest the entailed
//!    DEFINING equations `(= v rhs)` (`v` a bare string variable, `rhs` not a
//!    variable) into [`Executor::w7_defs`]. While that field is set, four W4
//!    helpers unwrap a defined variable into its defining term:
//!    [`Executor::w4_origin`] (so a position of `_EXTEND_VAR_0` resolves to a
//!    position of `ip_str`), [`Executor::w4_window_root`],
//!    [`Executor::w4_mentions`], and [`Executor::w4_violations`] (which scores
//!    the CLOSURE of an assignment, so a stale defined variable can never make a
//!    candidate look good). Synthesis then runs over the FREE variables only —
//!    the defined ones are recomputed by [`Executor::w7_propagate_defs`] from
//!    their own right-hand sides, using AY's evaluator, so the propagation
//!    cannot disagree with the validation that follows. This is the joint
//!    position + digit generator shape A needs: W5's placements move the `":"`
//!    separators inside `ip_str`, W6's numeric fills write digits into the
//!    fields those separators carve out, and both are scored against the same
//!    closure in one candidate.
//!    Four repair/seed moves ride that unwrapping, all of which every W4/W5/W6
//!    arm structurally declines:
//!    * **SEGMENTATION seeds** ([`Executor::w7_seeds`]) — `k` fields joined by
//!      the literal an `str.indexof` reads. A chain keyed on separators has no
//!      fields at all until they exist, so every per-position seed scores
//!      identically badly. Seeds are PRE-SCORED and searched best-first (one
//!      scoring call is a closure plus an atom sweep; one full synthesis is
//!      thousands of them).
//!    * **A class-membership arm** ([`Executor::w7_repair_candidates`]) —
//!      `(str.contains "0123456789ABCDEFabcdef" (str.at W i))`, the class test
//!      spelled with the CLASS as the haystack. W4's `str.contains` arm asks
//!      for the origin of `args[0]`, which is a constant here, and declines.
//!    * **A length arm** ([`Executor::w7_length_fills`]) — `(< (+ (+ 0 1) 1)
//!      (str.len W))`, a bound written as an arithmetic TERM. W4's length arm
//!      needs an integer literal; W6's nudge needs a numerically-read variable.
//!    * **INT definition closure** ([`Executor::w7_fill_int_defs`]) — an Int
//!      variable with no arithmetic model evaluates to 0, not Unknown, so a
//!      branch's `(= len_0 (str.len idx_0))` scored a correct witness as
//!      violated.
//! 2. **Branch selection + Boolean closure (shape B).** The kaluza family hides
//!    every definition and membership inside `(ite c (and …) …)` — or its
//!    rewritten `(or (not c) (and …))` — whose condition the forced-literal
//!    closure does not resolve, so the entailed atom set is two bookkeeping
//!    equalities. [`Executor::w7_branch_atoms`] offers bounded MIXED-RADIX
//!    combinations of branch arms as extra atoms, each carrying the Boolean pin
//!    its arm implies, and [`Executor::w7_close_bool_pins`] closes those pins
//!    under the formula's own Boolean definitions (`T_3 = ¬T_2`,
//!    `T_2 = (c = false)`). A selection is a SEARCH HINT: the candidate it
//!    produces is decided by the full validation battery over the whole formula.
//! 3. **Position-coupling closure (shape B).**
//!    [`Executor::w7_coupling_seeds`] solves the Leetcode `partition` family's
//!    `(= (str.at s i) (str.at s j))` atoms TOGETHER — union the positions a
//!    positive coupling joins, give each class its own character — instead of
//!    one edit per atom, which is what makes that plateau wide.
//! 4. **Multi-atom placement search (shape B).**
//!    [`Executor::w7_multi_placement_search`] generalises W5's loop to K > 1
//!    simultaneous placements: a bounded beam over placement DEPTH (≤
//!    [`MAX_W7_PLACE_DEPTH`]) that lets an intermediate step fail to improve —
//!    which is exactly what a wide plateau requires — while the ACCEPTED result
//!    must still strictly improve on the plateau it started from.
//!    MEASURED NEUTRAL on the shipped residue: ablating it converts the same
//!    six files, so no conversion here is attributable to it. It is kept
//!    because it is bounded, costs no measured regression (0 losses on the
//!    600-file sweep with it enabled), and is the only machinery present for a
//!    plateau that genuinely needs two placements at once.
//! 5. **Witness enumeration (shape C).**
//!    [`ay_strings::we_regex::find_witnesses_bounded`] extends the existing
//!    derivative BFS to yield successive DISTINCT accepting words at a given
//!    length (`find_witness_bounded` is now that function with `want = 1`, and
//!    returns the same first word). W7 builds a length-grouped word pool per
//!    variable and emits ROTATED joint candidates, so two variables sharing a
//!    language get different words of the same length.
//!
//! ## Measured (600-file QF_S + QF_SLIA canary, `ay solve --self-check -T:20`)
//!
//! Six conversions, every one confirmed by AY's own fail-closed self-check, and
//! ZERO losses / zero soundness flips against the same sweep with the flag off:
//! `ip_int_from_string` 32 / 383 / 438 (chain search), Leetcode `partition`
//! (coupling closure), kaluza `bettermatch1` (branch selection + Boolean/Int
//! closure), stringfuzz `regex-026` (witness enumerator). Flags-off identity is
//! exact: 600/600 verdicts unchanged.
//!
//! ## Budget
//!
//! W7 takes at most [`W7_MAX_BUDGET`], and never more than a
//! [`W7_BUDGET_SHARE`]-th of the solve's remaining time, then RESTORES the outer
//! deadline before validating. Both halves are load-bearing and both were
//! measured: without a budget, `ip_int_from_string__454` (already solved) became
//! a timeout; without the restore, `ip_int_from_string__383` built six
//! self-consistent witnesses and validated none of them, because
//! `w4_validate_candidates` polls `should_abort_theory_loop` before each
//! candidate.
//!
//! ## Soundness contract (inherited from W4/W5/W6, NOT weakened)
//!
//! * **No inner solve.** W7 never pins a candidate as an assumption and
//!   re-solves. That route was measured leaking a refutation into the outer
//!   verdict — a wrong `unsat` on `kaluza/sat/small/bettermatch1`, which is
//!   itself one of the files W7 targets. W7 is construct-and-validate only, via
//!   [`Executor::w4_validate_candidates`].
//! * **A failed construction never justifies UNSAT.** The only outcomes are a
//!   fully validated model or `Ok(None)`.
//! * **Memo discipline.** Every trial-model epoch is bracketed by
//!   [`w4_memo_reset`] (`evaluate_term` memoizes by `TermId` alone, and W7's
//!   trial models change on every propagation round).
//! * **No guard removed, nothing relaxed.** [`Executor::w7_defs`] is `None`
//!   outside this pass, so W4/W5/W6 and every gate are byte-identical with
//!   `AY_STR_W7` unset; the definition-unwrapping only ever changes which
//!   CANDIDATES are built, never which are accepted.
//! * **Branch selections and Boolean/Int pins are model CONTENT, not
//!   assumptions.** They ride `Model::bool_overrides` / `Model::lia_model` —
//!   the slots model completion and array reconciliation already use — and are
//!   DERIVED from the candidate by AY's own evaluator. A wrong selection makes
//!   a candidate the battery rejects; it can never make one it accepts.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermId};
use ay_core::Sort;
use ay_strings::we_regex::{find_witnesses_bounded, WeRegex};

use crate::executor_types::{Result, SolveResult};

use super::super::Executor;
use super::strings_w4::{w4_memo_reset, MAX_W4_LEN};

/// Master switch (default ON, `AY_STR_W7=0` kill switch → byte-identical to W6-only).
pub(in crate::executor) fn str_w7_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: 6 further conversions (3 ip_int_from_string, Leetcode
    // partition, kaluza bettermatch1, stringfuzz regex-026), EVERY ONE
    // confirmed by AY's own fail-closed --self-check; 600-file sweep 6 gains /
    // 0 losses / 0 soundness flips; flags-off identity measured 600/600.
    // AY_STR_W7=0 is the kill switch.
    *V.get_or_init(|| !matches!(std::env::var("AY_STR_W7").ok().as_deref(), Some("0")))
}

/// String variables W7 will handle jointly.
const MAX_W7_VARS: usize = 24;

/// Defining equations followed.
const MAX_W7_DEFS: usize = 24;

/// Propagation rounds per closure. The `full_str_int` chains are one level
/// deep (every `_EXTEND_VAR_i` reads `ip_str` directly); the kaluza
/// `T_1 = T1_4 ++ T2_4`, `T2_4 = var_0xINPUT` chains are three or four.
const MAX_W7_PROP_ROUNDS: usize = 8;

/// Longest value W7 will record for a DEFINED variable. Bigger than
/// [`MAX_W4_LEN`] (which bounds what the climb WRITES): a defined variable is a
/// concatenation of several free ones and is only ever read back.
const MAX_W7_DEF_LEN: usize = 4096;

/// Entailed atoms carried into the repair loop.
const MAX_W7_ATOMS: usize = 512;

/// Seed assignments attempted.
const MAX_W7_SEEDS: usize = 32;

/// Atom sets W7 will search (the entailed closure, plus branch selections).
const MAX_W7_BRANCH_SETS: usize = 6;

/// Wall-clock ceiling on the whole W7 pass (it also never takes more than
/// [`W7_BUDGET_SHARE`] of whatever the solve has left).
///
/// Deliberately small. W7 can only ever produce a SAT witness, so on an UNSAT
/// file every second it spends is a second taken from the refutation search
/// that follows it — and the `full_str_int` family it targets contains BOTH
/// (`ip_int_from_string` is sat, `leetcode_int-restoreIpAddresses` is unsat and
/// takes ~14 s of a 20 s budget to refute).
const W7_MAX_BUDGET: std::time::Duration = std::time::Duration::from_secs(5);

/// Fraction of the remaining solve time W7 may take.
const W7_BUDGET_SHARE: u32 = 3;

/// Distinct characters the coupling closure colours position classes with.
const W7_COUPLING_ALPHABET: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

/// Coupling-closure seeds built per pass.
const MAX_W7_COUPLING_SEEDS: usize = 4;

/// Lengths probed per variable by the coupling closure.
const MAX_W7_COUPLING_LENGTHS: usize = 3;

/// Characters proposed per class-membership repair.
const MAX_W7_CLASS_CHOICES: usize = 6;

/// Self-consistent joint assignments handed to validation. Small on purpose:
/// each one costs a full validation battery, and the search that builds the
/// next one is what the W7 budget is for.
const MAX_W7_CANDIDATES: usize = 4;

/// Simultaneous placements the multi-atom search may stack.
pub(super) const MAX_W7_PLACE_DEPTH: usize = 3;

/// Placements expanded at the multi-atom search's first level.
const MAX_W7_PLACE_WIDTH: usize = 20;

/// Trials kept as the beam between levels.
const MAX_W7_PLACE_BEAM: usize = 3;

/// Violated atoms above which a plateau is "wrong basin", not "wide".
const MAX_W7_ENTRY_VIOLATIONS: usize = 8;

/// Separator fields the segmentation seeds build.
const MAX_W7_FIELDS: usize = 10;

/// Distinct words enumerated per (variable, length).
const MAX_W7_WORDS_PER_LEN: usize = 4;

/// Lengths probed by the distinct-witness enumerator.
const MAX_W7_WORD_LEN: usize = 12;

/// Rotated joint candidates the distinct-witness construction emits.
const MAX_W7_WORD_CANDIDATES: usize = 12;

/// Derivative-BFS depth for the distinct-witness enumerator.
const MAX_W7_WITNESS_DEPTH: usize = 16;

impl Executor {
    // ─────────────────────────── the W7 pre-pass ──────────────────────────

    /// W7 pre-pass. Returns `Ok(Some(Sat))` only for a model the full
    /// validation battery confirmed, `Ok(None)` otherwise — never `Unsat`.
    pub(in crate::executor) fn try_w7_witnesses(&mut self) -> Result<Option<SolveResult>> {
        if !str_w7_enabled() || self.pivot_enum_depth != 0 {
            return Ok(None);
        }
        let vars = self.collect_string_variables();
        if vars.is_empty() || vars.len() > MAX_W7_VARS {
            if super::debug_auflia_enabled() {
                safe_eprintln!(
                    "[W7] declined: {} string var(s), joint work bound {MAX_W7_VARS}",
                    vars.len()
                );
            }
            return Ok(None);
        }

        // (3) shape C first: it is cheap (a bounded BFS over the memberships)
        // and it needs no atom closure at all.
        if let Some(r) = self.w7_try_distinct_words(&vars)? {
            return Ok(Some(r));
        }

        let (forced_true, forced_false) = self.forced_literal_closure_ext(true);
        let base = self.w7_atoms(&forced_true, &forced_false);
        if base.is_empty() {
            return Ok(None);
        }

        // W7'S OWN BUDGET. W7 is the LAST pass, so whatever it does not finish
        // it simply hands back — but an unbounded W7 spends the WHOLE remaining
        // solve on one seed and starves the pipeline that runs after it
        // (measured: `ip_int_from_string__454`, already solved, degraded to a
        // timeout when W7 ran without one). Half the remaining time, capped, and
        // the outer deadline is restored on every exit path.
        let saved_deadline = self.solve_deadline.get();
        let saved_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        if let Some(sub) = w7_sub_deadline(saved_deadline) {
            self.solve_deadline.set(Some(sub));
        }

        // BRANCH SELECTIONS. The kaluza family hides every definition and every
        // membership inside a top-level `(ite c (and …) …)` whose condition the
        // forced-literal closure does not resolve, so the entailed atom set is
        // two bookkeeping equalities and W7 sees nothing to propagate. Each
        // selection ADDS a branch's conjuncts as if they were entailed; the
        // candidate that results is still decided by the full validation
        // battery over the WHOLE formula, so a wrong branch guess costs bounded
        // time and can never produce a verdict.
        let mut atom_sets: Vec<(Vec<(TermId, bool)>, HashMap<TermId, bool>)> =
            vec![(base.clone(), HashMap::default())];
        for (extra, pins) in self.w7_branch_atoms() {
            if atom_sets.len() >= MAX_W7_BRANCH_SETS {
                break;
            }
            let mut merged = base.clone();
            for a in extra {
                if !merged.contains(&a) && merged.len() < MAX_W7_ATOMS {
                    merged.push(a);
                }
            }
            if merged.len() != base.len() {
                atom_sets.push((merged, pins));
            }
        }

        let mut outcome: Option<SolveResult> = None;
        for (atoms, bool_pins) in atom_sets {
            if outcome.is_some() || self.should_abort_theory_loop() {
                break;
            }
            let defs = self.w7_collect_defs(&atoms, &vars);
            let free: Vec<TermId> = vars
                .iter()
                .copied()
                .filter(|v| !defs.contains_key(v))
                .collect();
            if free.is_empty() {
                continue;
            }
            // POSITION-COUPLING seeds (the Leetcode `partition` family): a
            // formula whose whole content is `(= (str.substr s i 1)
            // (str.substr s j 1))` atoms, positive and negative, over ONE
            // variable. There is nothing to propagate, so the definition search
            // has no reason to run — but the couplings are exactly the
            // multi-atom shape a one-edit-per-atom climb cannot close.
            let couplings = self.w7_coupling_seeds(&free, &atoms);
            // W7's synthesis is only different from W4's when there is
            // something to propagate or a coupling closure to seed from.
            // Without either, W4/W5/W6 have already done exactly this work.
            if defs.is_empty() && couplings.is_empty() {
                continue;
            }
            // The separator literals are harvested from the FULL set first: the
            // `str.indexof … ":"` reads that name them live INSIDE the defining
            // equations, which is exactly what the filter below removes.
            let separators = self.w7_separators(&atoms);
            // The DEFINING equations themselves drop out of the scored set: the
            // closure satisfies each of them by construction, so evaluating
            // them is pure cost — and they are by far the most expensive atoms
            // in the set (the `ip_int_from_string` chain is a 1 MB nest of
            // `str.substr` over `str.indexof`, re-walked on every scoring
            // call). Nothing is trusted because of this:
            // `finalize_sat_model_validation` still evaluates the WHOLE
            // formula, defining equations included, before any `sat`.
            let atoms: Vec<(TermId, bool)> = atoms
                .into_iter()
                .filter(|&(t, pol)| !(pol && self.w7_is_def_atom(t, &defs)))
                .collect();
            if super::debug_auflia_enabled() {
                safe_eprintln!(
                    "[W7] {} atom(s), {} definition(s), {} free var(s) of {}",
                    atoms.len(),
                    defs.len(),
                    free.len(),
                    vars.len()
                );
            }

            // ARMED — and armed BEFORE the analysis, not just before the
            // search. `w4_mentions` and `w6_numeric_vars` both have to see
            // THROUGH the definitions: every per-position atom of this family
            // names only a DEFINED variable (`_EXTEND_VAR_0`), so without the
            // unwrapping the free variable's atom set is just its own defining
            // equations and the climb has nothing to repair.
            self.w7_defs = Some(defs);
            self.w7_int_defs = self.w7_collect_int_defs(&atoms);

            let alphabet = self.collect_alphabet();
            let fresh = w7_fresh_char(&alphabet);
            let numeric = self.w6_numeric_vars(&free, &atoms);
            let var_atoms: Vec<(TermId, Vec<(TermId, bool)>)> = free
                .iter()
                .map(|&v| {
                    let mine: Vec<(TermId, bool)> = atoms
                        .iter()
                        .copied()
                        .filter(|&(t, _)| self.w4_mentions(t, v, 0))
                        .collect();
                    (v, mine)
                })
                .collect();
            let mut seeds = self.w7_seeds(&free, &atoms, &separators, fresh);
            w7_prepend_coupling_seeds(&couplings, &free, &mut seeds);
            let candidates = self.w7_search(&var_atoms, &atoms, &seeds, &alphabet, &numeric, fresh);
            if candidates.is_empty() {
                self.w7_defs = None;
                self.w7_int_defs.clear();
                continue;
            }
            // NOTE: `w7_defs` / `w7_int_defs` stay ARMED across validation.
            // `w4_model_of` is what puts the derived Int values into the
            // candidate's `LiaModel`, and disarming first left
            // `PCTEMP_LHS_1_len_0` at the Int default of 0 — which makes the
            // kaluza branch conjunct `(= len_0 (str.len idx_0))` false and
            // rejects a witness that is correct.
            // Validation runs OUTSIDE the W7 sub-deadline: `w4_validate_candidates`
            // polls `should_abort_theory_loop` before each candidate, so an
            // expired W7 budget would throw away every witness W7 just built
            // (measured on `ip_int_from_string__383`: 6 self-consistent
            // candidates, none ever validated).
            self.solve_deadline.set(saved_deadline);
            self.last_unknown_reason = saved_reason;
            self.last_result = saved_result.clone();
            if super::debug_auflia_enabled() {
                safe_eprintln!(
                    "[W7] {} self-consistent joint candidate(s)",
                    candidates.len()
                );
            }
            let mut pins = bool_pins.clone();
            if let Some(first) = candidates.first() {
                self.w7_close_bool_pins(first, &atoms, &mut pins);
            }
            // Not `?`: an error must not escape with `w7_defs` still armed and
            // the W7 sub-deadline still installed — the rest of the solve would
            // then run with W7's search state and a truncated budget.
            let validated = self.w4_validate_candidates_with_bools(&candidates, &pins);
            self.w7_defs = None;
            self.w7_int_defs.clear();
            outcome = match validated {
                Ok(v) => v,
                Err(e) => {
                    self.solve_deadline.set(saved_deadline);
                    w4_memo_reset();
                    return Err(e);
                }
            };
            if outcome.is_none() {
                // Next selection gets what is left of the W7 budget.
                self.last_unknown_reason = saved_reason;
                self.last_result = saved_result.clone();
                if let Some(sub) = w7_sub_deadline(saved_deadline) {
                    self.solve_deadline.set(Some(sub));
                }
            }
        }

        self.solve_deadline.set(saved_deadline);
        self.w7_defs = None;
        self.w7_int_defs.clear();
        w4_memo_reset();
        // A W7 sub-deadline break is not the SOLVE's timeout: restore the
        // unknown bookkeeping so the pipeline after W7 reports its own reason.
        if outcome.is_none() {
            self.last_unknown_reason = saved_reason;
            self.last_result = saved_result;
        }
        Ok(outcome)
    }

    /// The seeded synthesis loop, run with [`Executor::w7_defs`] armed.
    fn w7_search(
        &mut self,
        var_atoms: &[(TermId, Vec<(TermId, bool)>)],
        atoms: &[(TermId, bool)],
        seeds: &[HashMap<TermId, String>],
        alphabet: &[char],
        numeric: &HashSet<TermId>,
        fresh: char,
    ) -> Vec<HashMap<TermId, String>> {
        // PRE-SCORE the seeds and search the most promising first. One scoring
        // call is a definition closure plus an atom sweep; one full synthesis
        // from a seed is thousands of them. Measured on
        // `ip_int_from_string__32`: the seed that converts (eight four-digit
        // fields) is the eleventh in generation order, and searching the ten
        // ahead of it costs more than the whole W7 budget.
        let mut ranked: Vec<(usize, &HashMap<TermId, String>)> = seeds
            .iter()
            .take(MAX_W7_SEEDS)
            .map(|s| (self.w4_violations(atoms, s), s))
            .collect();
        ranked.sort_by_key(|&(score, _)| score);

        let mut candidates: Vec<HashMap<TermId, String>> = Vec::new();
        for (i, (_, seed)) in ranked.into_iter().enumerate() {
            if self.should_abort_theory_loop() {
                break;
            }
            let mut assign = seed.clone();
            self.w4_synthesize(var_atoms, &mut assign, alphabet, numeric, fresh);
            let mut viol = self.w4_violations(atoms, &assign);
            if viol != 0 {
                // W5's single-needle placement first (it is the cheaper search
                // and owns every plateau one placement can cross)…
                self.w5_placement_search(var_atoms, atoms, &mut assign, alphabet, numeric, fresh);
                viol = self.w4_violations(atoms, &assign);
            }
            if viol != 0 {
                // …then W7's multi-atom generalisation for the wide plateau.
                self.w7_multi_placement_search(
                    var_atoms,
                    atoms,
                    &mut assign,
                    alphabet,
                    numeric,
                    fresh,
                );
                viol = self.w4_violations(atoms, &assign);
            }
            if super::debug_auflia_enabled() {
                let mut closed = assign.clone();
                self.w7_propagate_defs(&mut closed);
                let mut shown: Vec<String> = closed
                    .iter()
                    .map(|(k, v)| format!("{}={v:?}", k.index()))
                    .collect();
                shown.sort();
                safe_eprintln!("[W7] seed {i}: violations={viol} {shown:?}");
            }
            if viol != 0 {
                continue;
            }
            // Hand validation the CLOSURE: the defined variables carry the
            // values their own equations give them.
            self.w7_propagate_defs(&mut assign);
            if !candidates
                .iter()
                .any(|c: &HashMap<TermId, String>| w7_same(c, &assign))
            {
                candidates.push(assign);
                if candidates.len() >= MAX_W7_CANDIDATES {
                    break;
                }
            }
        }
        candidates
    }

    // ──────────────────────── definitions and closure ─────────────────────

    /// The defining right-hand side of `term`, when W7 is armed and `term` is a
    /// defined string variable. `None` everywhere else — this is the single
    /// place the four W4 helpers consult.
    pub(super) fn w7_def_of(&self, term: TermId) -> Option<TermId> {
        self.w7_defs.as_ref()?.get(&term).copied()
    }

    /// Recompute every DEFINED variable from its own right-hand side, to a
    /// small fixpoint, using AY's evaluator (so the closure cannot disagree
    /// with the validation that decides the candidate).
    ///
    /// Bracketed by [`w4_memo_reset`] on both sides: the trial model changes on
    /// every round and `evaluate_term` memoizes by `TermId` alone.
    pub(super) fn w7_propagate_defs(&self, assign: &mut HashMap<TermId, String>) {
        let Some(defs) = self.w7_defs.as_ref() else {
            return;
        };
        if defs.is_empty() {
            return;
        }
        let mut ordered: Vec<(TermId, TermId)> = defs.iter().map(|(&v, &r)| (v, r)).collect();
        ordered.sort_by_key(|(v, _)| v.index());
        // FLAT chain (no definition reads another defined variable): one round
        // is a fixpoint, and the confirming round is a second full walk of the
        // deep `str.substr`/`str.indexof` nest for nothing.
        let flat = !ordered
            .iter()
            .any(|&(_, rhs)| ordered.iter().any(|&(v, _)| self.w7_reads(rhs, v, 0)));
        let rounds = if flat { 1 } else { MAX_W7_PROP_ROUNDS };
        for _round in 0..rounds {
            let mut changed = false;
            let model = super::strings_w4::w4_trial_model(assign);
            w4_memo_reset();
            for &(var, rhs) in &ordered {
                let Some(v) = self.w4_eval_string(&model, rhs) else {
                    continue;
                };
                if v.chars().count() <= MAX_W7_DEF_LEN && assign.get(&var) != Some(&v) {
                    assign.insert(var, v);
                    changed = true;
                }
            }
            w4_memo_reset();
            if !changed {
                break;
            }
        }
    }

    /// Close a candidate's BOOLEAN pins under the formula's Boolean
    /// definitions.
    ///
    /// The `kaluza` family encodes its branch condition indirectly:
    /// `(assert T_3)`, `(= T_3 (not T_2))`, `(= T_2 (= PCTEMP_LHS_1 false))`.
    /// Pinning only the branch condition leaves `T_2`/`T_3` unassigned, they
    /// evaluate to Unknown, and the asserted `T_3` is never confirmed — so the
    /// candidate is rejected even though its string values are a witness.
    /// Every value here is DERIVED from the candidate by AY's own evaluator, so
    /// the closure cannot disagree with the validation that decides it.
    fn w7_close_bool_pins(
        &self,
        cand: &HashMap<TermId, String>,
        atoms: &[(TermId, bool)],
        pins: &mut HashMap<TermId, bool>,
    ) {
        // Asserted Boolean literals are pinned outright.
        for &t in &self.ctx.assertions {
            match self.ctx.terms.get(t) {
                TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::Bool => {
                    pins.insert(t, true);
                }
                TermData::Not(inner) if *self.ctx.terms.sort(*inner) == Sort::Bool => {
                    if matches!(self.ctx.terms.get(*inner), TermData::Var(..)) {
                        pins.insert(*inner, false);
                    }
                }
                _ => {}
            }
        }
        // `(= b e)` definitions, to a small fixpoint.
        let mut defs: Vec<(TermId, TermId)> = Vec::new();
        for &(t, pol) in atoms {
            if !pol || defs.len() >= MAX_W7_DEFS {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                if matches!(self.ctx.terms.get(lhs), TermData::Var(..))
                    && *self.ctx.terms.sort(lhs) == Sort::Bool
                    && !matches!(self.ctx.terms.get(rhs), TermData::Var(..))
                    && !defs.iter().any(|&(v, _)| v == lhs)
                {
                    defs.push((lhs, rhs));
                    break;
                }
            }
        }
        defs.sort_by_key(|(v, _)| v.index());
        for _round in 0..MAX_W7_PROP_ROUNDS {
            let mut changed = false;
            let mut model = self.w4_model_of(cand);
            model.bool_overrides = pins.clone();
            w4_memo_reset();
            for &(var, rhs) in &defs {
                if let super::super::model::EvalValue::Bool(b) = self.evaluate_term(&model, rhs) {
                    if pins.get(&var) != Some(&b) {
                        pins.insert(var, b);
                        changed = true;
                    }
                }
            }
            w4_memo_reset();
            if !changed {
                break;
            }
        }
    }

    /// Fill `model`'s `LiaModel` from W7's INT defining equations.
    ///
    /// An Int variable with no arithmetic model evaluates to 0, not Unknown —
    /// so the `kaluza` branch conjunct `(= PCTEMP_LHS_1_len_0 (str.len idx_0))`
    /// scores as definitively VIOLATED against a string witness that actually
    /// satisfies it. Deriving the Int from its own defining equation, with AY's
    /// evaluator, keeps the trial model and the validation that follows in
    /// agreement. No-op outside W7's own pass.
    pub(super) fn w7_fill_int_defs(&self, model: &mut super::super::model::Model) {
        if self.w7_int_defs.is_empty() {
            return;
        }
        let mut values: HashMap<TermId, num_bigint::BigInt> = HashMap::default();
        let mut ordered: Vec<(TermId, TermId)> =
            self.w7_int_defs.iter().map(|(&v, &r)| (v, r)).collect();
        ordered.sort_by_key(|(v, _)| v.index());
        for _round in 0..2 {
            let mut changed = false;
            model.lia_model = Some(ay_lia::LiaModel {
                values: values.clone(),
            });
            w4_memo_reset();
            for &(var, rhs) in &ordered {
                if let super::super::model::EvalValue::Rational(r) = self.evaluate_term(model, rhs)
                {
                    if r.is_integer() {
                        let v = r.to_integer();
                        if values.get(&var) != Some(&v) {
                            values.insert(var, v);
                            changed = true;
                        }
                    }
                }
            }
            w4_memo_reset();
            if !changed {
                break;
            }
        }
        model.lia_model = Some(ay_lia::LiaModel { values });
    }

    /// Entailed `(= v e)` definitions of INT variables.
    fn w7_collect_int_defs(&self, atoms: &[(TermId, bool)]) -> HashMap<TermId, TermId> {
        let mut out: HashMap<TermId, TermId> = HashMap::default();
        for &(t, pol) in atoms {
            if !pol || out.len() >= MAX_W7_DEFS {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                if !matches!(self.ctx.terms.get(lhs), TermData::Var(..))
                    || *self.ctx.terms.sort(lhs) != Sort::Int
                    || out.contains_key(&lhs)
                    || rhs == lhs
                    || self.w7_reads(rhs, lhs, 0)
                {
                    continue;
                }
                out.insert(lhs, rhs);
                break;
            }
        }
        out
    }

    /// Entailed DEFINING equations: `(= v rhs)` with `v` a bare string variable
    /// of the formula and `rhs` a non-variable string term that does not read
    /// `v` back.
    ///
    /// Only POSITIVE entailed equalities qualify, and the first definition of a
    /// variable wins — a second one is a constraint the search must satisfy,
    /// not a second definition.
    fn w7_collect_defs(
        &self,
        atoms: &[(TermId, bool)],
        vars: &[TermId],
    ) -> HashMap<TermId, TermId> {
        let known: HashSet<TermId> = vars.iter().copied().collect();
        let mut out: HashMap<TermId, TermId> = HashMap::default();
        for &(t, pol) in atoms {
            if !pol || out.len() >= MAX_W7_DEFS {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                if !matches!(self.ctx.terms.get(lhs), TermData::Var(..))
                    || *self.ctx.terms.sort(lhs) != Sort::String
                    || !known.contains(&lhs)
                    || out.contains_key(&lhs)
                {
                    continue;
                }
                // A bare `(= x y)` IS taken as a definition of `x` — the
                // kaluza family writes `(= group_1 idx_0)` and the witness is
                // "copy". Only ONE orientation is ever recorded (the `break`
                // below plus the already-defined guard above), and the cycle
                // sweep at the end drops anything that closes a loop.
                if rhs == lhs {
                    continue;
                }
                // Self-referential right-hand sides are equations to satisfy,
                // never definitions to evaluate.
                if self.w7_reads(rhs, lhs, 0) {
                    continue;
                }
                out.insert(lhs, rhs);
                break;
            }
        }
        // Break any residual cycle across definitions (a → b → a): drop the
        // variable with the larger index until every chain bottoms out.
        loop {
            let cyclic: Option<TermId> =
                out.keys().copied().find(|&v| self.w7_cyclic(&out, v, v, 0));
            match cyclic {
                Some(v) => {
                    out.remove(&v);
                }
                None => break,
            }
        }
        out
    }

    /// Atom sets contributed by a BRANCH SELECTION over the formula's top-level
    /// `ite` assertions.
    ///
    /// The kaluza `bettermatch`/`corecstrs` family asserts
    /// `(ite PCTEMP_LHS_1 (and (= var (str.++ T0 T1)) (str.in_re idx …) …) …)`
    /// and constrains `PCTEMP_LHS_1` only INDIRECTLY (`T_2 = (= PCTEMP_LHS_1
    /// false)`, `T_3 = (not T_2)`, `T_3`). The forced-literal closure does not
    /// resolve that, so the entailed atom set is two bookkeeping equalities and
    /// nothing in W4/W5/W6/W7 has a definition or a membership to work with.
    ///
    /// Two selections are offered — every `ite` taken THEN, and every `ite`
    /// taken ELSE — which is all this family needs (its conditions are the same
    /// literal). A selection is a SEARCH HINT, never an assumption: the
    /// candidate it produces is decided by the full validation battery over the
    /// whole formula, branch condition included.
    fn w7_branch_atoms(&self) -> Vec<(Vec<(TermId, bool)>, HashMap<TermId, bool>)> {
        // A BRANCH POINT is a top-level assertion that offers alternatives: an
        // `ite`'s two arms, or a disjunction's disjuncts (the shape an
        // `(ite c A true)` is rewritten into upstream).
        // Each point is a list of (arm, implied Boolean pin).
        let mut points: Vec<Vec<(TermId, Option<(TermId, bool)>)>> = Vec::new();
        for &t in &self.ctx.assertions {
            if points.len() >= MAX_W7_DEFS {
                break;
            }
            let bool_var = |c: TermId| -> bool {
                matches!(self.ctx.terms.get(c), TermData::Var(..))
                    && *self.ctx.terms.sort(c) == Sort::Bool
            };
            match self.ctx.terms.get(t) {
                TermData::Ite(c, a, b) => {
                    let (c, a, b) = (*c, *a, *b);
                    let pin = |v: bool| bool_var(c).then_some((c, v));
                    points.push(vec![(a, pin(true)), (b, pin(false))]);
                }
                TermData::App(Symbol::Named(n), args) if n == "ite" && args.len() == 3 => {
                    let c = args[0];
                    let pin = |v: bool| bool_var(c).then_some((c, v));
                    points.push(vec![(args[1], pin(true)), (args[2], pin(false))]);
                }
                TermData::App(Symbol::Named(n), args) if n == "or" && args.len() >= 2 => {
                    // `(ite c A true)` arrives rewritten as `(or (not c) A)`:
                    // choosing the `A` arm means `c` is TRUE, and choosing the
                    // `(not c)` arm means `c` is false.
                    let negated: Vec<TermId> = args
                        .iter()
                        .filter_map(|&d| match self.ctx.terms.get(d) {
                            TermData::Not(inner) if bool_var(*inner) => Some(*inner),
                            _ => None,
                        })
                        .collect();
                    points.push(
                        args.iter()
                            .map(|&d| {
                                let pin = match self.ctx.terms.get(d) {
                                    TermData::Not(inner) if bool_var(*inner) => {
                                        Some((*inner, false))
                                    }
                                    _ if bool_var(d) => Some((d, true)),
                                    // A non-literal arm of `(or (not c) A)`
                                    // is taken only when `c` holds.
                                    _ => negated.first().map(|&v| (v, true)),
                                };
                                (d, pin)
                            })
                            .collect(),
                    );
                }
                _ => {}
            }
        }
        if points.is_empty() {
            return Vec::new();
        }
        // COMBINATIONS, not a diagonal. The kaluza shape has two branch points
        // that arrive in different spellings — one `(ite c (and …) …)` and one
        // rewritten to `(or (not c) (and …))` — so the conjunct-carrying arm is
        // at index 0 of one and index 1 of the other, and a uniform choice
        // index picks up neither pair. Mixed-radix, hard-capped.
        let mut out: Vec<(Vec<(TermId, bool)>, HashMap<TermId, bool>)> = Vec::new();
        for combo in 0..MAX_W7_BRANCH_SETS {
            let mut set: Vec<(TermId, bool)> = Vec::new();
            let mut pins: HashMap<TermId, bool> = HashMap::default();
            let mut rest = combo;
            let mut consistent = true;
            for alts in &points {
                let radix = alts.len().max(1);
                let idx = rest % radix;
                rest /= radix;
                let Some(&(pick, pin)) = alts.get(idx).or_else(|| alts.first()) else {
                    continue;
                };
                if let Some((v, b)) = pin {
                    if pins.insert(v, b).is_some_and(|prev| prev != b) {
                        consistent = false; // two arms disagree about `v`
                    }
                }
                self.w7_flatten_conjuncts(pick, true, 0, &mut set);
            }
            if consistent && !set.is_empty() && !out.iter().any(|(s, _)| *s == set) {
                out.push((set, pins));
            }
        }
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W7] branch points: {}, selections: {}",
                points.len(),
                out.len()
            );
        }
        out
    }

    /// Flatten `and`/`not` structure into atoms with polarity, keeping only the
    /// predicate/equality shapes W7 scores.
    fn w7_flatten_conjuncts(
        &self,
        term: TermId,
        pol: bool,
        depth: usize,
        out: &mut Vec<(TermId, bool)>,
    ) {
        if depth > 16 || out.len() >= MAX_W7_ATOMS {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => self.w7_flatten_conjuncts(*inner, !pol, depth + 1, out),
            TermData::App(Symbol::Named(name), args) => {
                if name == "and" && pol {
                    for &a in args {
                        self.w7_flatten_conjuncts(a, pol, depth + 1, out);
                    }
                    return;
                }
                if name == "not" && args.len() == 1 {
                    self.w7_flatten_conjuncts(args[0], !pol, depth + 1, out);
                    return;
                }
                let interesting = matches!(
                    name.as_str(),
                    "=" | "distinct"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "str.contains"
                        | "str.prefixof"
                        | "str.suffixof"
                        | "str.in_re"
                        | "str.in.re"
                        | "str.<"
                        | "str.<="
                );
                if interesting && !args.is_empty() && !out.contains(&(term, pol)) {
                    out.push((term, pol));
                }
            }
            _ => {}
        }
    }

    /// Whether `atom` IS one of the harvested defining equations (either
    /// orientation).
    fn w7_is_def_atom(&self, atom: TermId, defs: &HashMap<TermId, TermId>) -> bool {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
            return false;
        };
        name == "="
            && args.len() == 2
            && [(args[0], args[1]), (args[1], args[0])]
                .into_iter()
                .any(|(l, r)| defs.get(&l) == Some(&r))
    }

    /// Whether `term` reads `var` (syntactically, bounded).
    fn w7_reads(&self, term: TermId, var: TermId, depth: usize) -> bool {
        if term == var {
            return true;
        }
        if depth > 48 {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::App(_, args) => args.iter().any(|&a| self.w7_reads(a, var, depth + 1)),
            TermData::Not(inner) => self.w7_reads(*inner, var, depth + 1),
            TermData::Ite(c, a, b) => {
                self.w7_reads(*c, var, depth + 1)
                    || self.w7_reads(*a, var, depth + 1)
                    || self.w7_reads(*b, var, depth + 1)
            }
            _ => false,
        }
    }

    /// Whether following `defs` from `from` can reach `target` again.
    fn w7_cyclic(
        &self,
        defs: &HashMap<TermId, TermId>,
        from: TermId,
        target: TermId,
        depth: usize,
    ) -> bool {
        if depth > MAX_W7_DEFS {
            return true; // unbounded chain — treat as cyclic and drop it.
        }
        let Some(&rhs) = defs.get(&from) else {
            return false;
        };
        for (&v, _) in defs.iter() {
            if v == from || !self.w7_reads(rhs, v, 0) {
                continue;
            }
            if v == target || self.w7_cyclic(defs, v, target, depth + 1) {
                return true;
            }
        }
        false
    }

    /// Entailed atoms worth evaluating — the same predicate/equality filter W4
    /// applies, kept local so W4's own harvest stays untouched.
    fn w7_atoms(&self, forced_true: &[TermId], forced_false: &[TermId]) -> Vec<(TermId, bool)> {
        let mut out: Vec<(TermId, bool)> = Vec::new();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        for (list, pol) in [(forced_true, true), (forced_false, false)] {
            for &t in list {
                if out.len() >= MAX_W7_ATOMS {
                    break;
                }
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                    continue;
                };
                if args.is_empty() {
                    continue;
                }
                let interesting = matches!(
                    name.as_str(),
                    "=" | "distinct"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "str.contains"
                        | "str.prefixof"
                        | "str.suffixof"
                        | "str.in_re"
                        | "str.in.re"
                        | "str.<"
                        | "str.<="
                );
                if interesting && seen.insert((t, pol)) {
                    out.push((t, pol));
                }
            }
        }
        out
    }

    // ───────────────────────────── seeding ────────────────────────────────

    /// Joint seeds for the FREE variables: W4's own per-variable pools, plus
    /// SEGMENTATION seeds — `k` fields joined by a separator literal the atoms
    /// mention — which is what a `str.indexof`-driven parse chain needs before
    /// any of its fields exist at all.
    fn w7_seeds(
        &self,
        free: &[TermId],
        atoms: &[(TermId, bool)],
        seps: &[String],
        fresh: char,
    ) -> Vec<HashMap<TermId, String>> {
        let pools = self.w4_seed_pools(free, atoms, fresh);
        let mut out: Vec<HashMap<TermId, String>> = Vec::new();
        // SEGMENTATION seeds FIRST. They are the targeted ones — a parse chain
        // keyed on `str.indexof` has no fields at all until the separators
        // exist, so every W4 pool value scores identically badly and would
        // otherwise spend the whole seed budget.
        for &var in free.iter().take(MAX_W7_VARS) {
            for sep in seps {
                // Field counts DESCENDING: a chain that splits k times needs at
                // least k+1 fields, and a longer seed can always lose a field
                // to the climb while a short one cannot gain one.
                for fields in (2..=MAX_W7_FIELDS).rev() {
                    // Field WIDTHS as well as counts: the `ip_int_from_string`
                    // fields are pinned to exactly four digits, and a seed of
                    // one-character fields makes the climb widen eight of them
                    // one character at a time.
                    for body in ["1", "1111", "z", "11"] {
                        let text = w7_segmented(sep, body, fields);
                        if text.chars().count() > MAX_W4_LEN {
                            continue;
                        }
                        let mut assign: HashMap<TermId, String> = HashMap::default();
                        for (v, pool) in &pools {
                            assign.insert(*v, pool.first().cloned().unwrap_or_default());
                        }
                        assign.insert(var, text);
                        w7_push_seed(assign, &mut out);
                    }
                }
            }
        }
        let depth = pools.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
        for idx in 0..depth {
            let mut assign: HashMap<TermId, String> = HashMap::default();
            for (var, pool) in &pools {
                let pick = pool.get(idx).or_else(|| pool.last());
                assign.insert(*var, pick.cloned().unwrap_or_default());
            }
            w7_push_seed(assign, &mut out);
        }
        out
    }

    /// Single-character-ish string literals the atoms use as SEPARATORS: the
    /// second argument of an `str.indexof` read. That is precisely the literal
    /// whose landing positions carve the parse chain's fields.
    fn w7_separators(&self, atoms: &[(TermId, bool)]) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut stack: Vec<(TermId, usize)> = atoms.iter().map(|&(t, _)| (t, 0)).collect();
        let mut budget = 4096usize;
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 || out.len() >= 4 {
                continue;
            }
            budget -= 1;
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                if name == "str.indexof" && args.len() == 3 {
                    if let Some(s) = self.w4_string_const(args[1]) {
                        if !s.is_empty() && s.chars().count() <= 2 && !out.contains(&s) {
                            out.push(s);
                        }
                    }
                }
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => {
                    for &a in args {
                        stack.push((a, depth + 1));
                    }
                }
                TermData::Not(inner) => stack.push((*inner, depth + 1)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, depth + 1));
                    stack.push((*a, depth + 1));
                    stack.push((*b, depth + 1));
                }
                _ => {}
            }
        }
        out
    }

    // ────────────────────── class-membership repair arm ───────────────────

    /// `(str.contains "0123456789ABCDEFabcdef" (str.at W i))` — a CHARACTER
    /// CLASS test spelled with the class as the HAYSTACK and the window as the
    /// needle. Every W4/W5/W6 arm declines it: W4's `str.contains` arm asks
    /// [`Executor::w4_origin`] for the position of `args[0]`, which here is a
    /// string constant, and W6 only reaches an atom that is numeric, a
    /// membership, or a negative pin.
    ///
    /// It is the whole shape of the `lib_int-ipaddress` / `full_str_int` parse
    /// chain's per-position constraints, on both polarities: positive asks for
    /// a class member at that position, negative asks for a non-member.
    ///
    /// Returns a LIST — "a digit" is a choice, not a single character, and W4's
    /// violation count picks.
    pub(super) fn w7_repair_candidates(
        &self,
        model: &super::super::model::Model,
        atom: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        fresh: char,
    ) -> Vec<Vec<char>> {
        let mut out: Vec<Vec<char>> = Vec::new();
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
            return out;
        };
        if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2 {
            self.w7_length_fills(model, name, args, pol, target, cur, fresh, &mut out);
            return out;
        }
        if name != "str.contains" || args.len() != 2 {
            return out;
        }
        // The class must be a ground literal and the needle a window of the
        // target; the reverse orientation is W4's own arm.
        let Some(class) = self.w4_string_const(args[0]) else {
            return out;
        };
        let Some(origin) = self.w4_origin(model, args[1], target, 0) else {
            return out;
        };
        let Some(have_s) = self.w4_eval_string(model, args[1]) else {
            return out;
        };
        let have = have_s.chars().count();
        if have == 0 || origin.checked_add(have).is_none_or(|e| e > cur.len()) {
            return out;
        }
        let class_chars: Vec<char> = class.chars().collect();
        let mut choices: Vec<char> = Vec::new();
        if pol {
            // Must be IN the class. Digits first: this family pairs the class
            // test with `(not (= (str.at W i) "a"))` for every letter, so a
            // digit is the only survivor.
            for &c in &class_chars {
                if c.is_ascii_digit() && !choices.contains(&c) {
                    choices.push(c);
                }
            }
            for &c in &class_chars {
                if !choices.contains(&c) {
                    choices.push(c);
                }
            }
        } else {
            // Must be OUT of the class.
            for c in [fresh, 'z', 'y', 'x', ':', '.', '_'] {
                if !class_chars.contains(&c) && !choices.contains(&c) {
                    choices.push(c);
                }
            }
        }
        for ch in choices.into_iter().take(MAX_W7_CLASS_CHOICES) {
            let mut next = cur.to_vec();
            next[origin] = ch;
            if next != cur && !out.contains(&next) {
                out.push(next);
            }
        }
        out
    }

    /// `(< (+ (+ (+ 0 1) 1) 1) (str.len _EXTEND_VAR_0))` — a length comparison
    /// whose OTHER side is an arithmetic TERM, not an integer literal.
    ///
    /// W4's length arm requires a literal (`TermData::Const(Int)`) and declines;
    /// W6's generalised nudge only fires for a variable some atom reads
    /// numerically. This family writes every bound as a `(+ … 1)` chain, so the
    /// window's required length is only visible by EVALUATING the other side —
    /// which is exactly what W7 does here, then resizes the window to the length
    /// that makes the comparison true.
    #[allow(clippy::too_many_arguments)]
    fn w7_length_fills(
        &self,
        model: &super::super::model::Model,
        op: &str,
        args: &[TermId],
        pol: bool,
        target: TermId,
        cur: &[char],
        fresh: char,
        out: &mut Vec<Vec<char>>,
    ) {
        for (side, other, len_on_left) in [(args[0], args[1], true), (args[1], args[0], false)] {
            let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(side) else {
                continue;
            };
            if f != "str.len" || fargs.len() != 1 {
                continue;
            }
            let Some(origin) = self.w4_origin(model, fargs[0], target, 0) else {
                continue;
            };
            let Some(have_s) = self.w4_eval_string(model, fargs[0]) else {
                continue;
            };
            let Some(bound) = self.w7_eval_int(model, other) else {
                continue;
            };
            let have = have_s.chars().count();
            // The comparison as WRITTEN, oriented so the window's length is the
            // left operand, then negated when the atom is entailed false.
            let want: i64 = match (op, len_on_left, pol) {
                // len OP bound
                ("<", true, true) | (">", false, true) => bound - 1,
                ("<=", true, true) | (">=", false, true) => bound,
                (">", true, true) | ("<", false, true) => bound + 1,
                (">=", true, true) | ("<=", false, true) => bound,
                // ¬(len OP bound)
                ("<", true, false) | (">", false, false) => bound,
                ("<=", true, false) | (">=", false, false) => bound + 1,
                (">", true, false) | ("<", false, false) => bound,
                (">=", true, false) | ("<=", false, false) => bound - 1,
                _ => continue,
            };
            let Ok(want) = usize::try_from(want) else {
                continue;
            };
            if want > MAX_W4_LEN || want == have {
                continue;
            }
            // Propose the exact length and one step toward it: a length atom
            // whose bound itself depends on lengths moves while we edit.
            let step = if want > have { have + 1 } else { have - 1 };
            for target_len in [want, step] {
                if target_len == have || target_len > MAX_W4_LEN {
                    continue;
                }
                if let Some(next) = w7_resize_window(cur, origin, have, target_len, fresh) {
                    if next != cur && !out.contains(&next) {
                        out.push(next);
                    }
                }
            }
        }
    }

    /// An integer-sorted term's value under the trial model.
    fn w7_eval_int(&self, model: &super::super::model::Model, term: TermId) -> Option<i64> {
        match self.evaluate_term(model, term) {
            super::super::model::EvalValue::Rational(r) if r.is_integer() => {
                i64::try_from(r.to_integer()).ok()
            }
            _ => None,
        }
    }

    // ───────────────── position-coupling closure (shape B) ────────────────

    /// Whole-value seeds built by CLOSING the per-position couplings of one
    /// variable at once.
    ///
    /// The Leetcode `partition` family is nothing but
    /// `(= (str.at s i) (str.at s j))` atoms, positive and negative — which
    /// reach the solver rewritten to `(= (str.substr s i 1) (str.substr s j 1))`
    /// (hence the origins are resolved through [`Executor::w4_origin`], never by
    /// matching `str.at` syntactically). W5 repairs ONE such coupling per edit,
    /// and each edit breaks another coupling that shares the position, so the
    /// climb plateaus with several violated atoms — the wide plateau.
    ///
    /// The closure solves them together: union the positions joined by a
    /// POSITIVE coupling, then give every class its own character. That
    /// satisfies every positive coupling by construction and every NEGATIVE
    /// coupling between distinct classes for free; a negative coupling INSIDE a
    /// class means this construction has no witness to offer and the seed is
    /// dropped (never a claim that none exists).
    fn w7_coupling_seeds(
        &self,
        free: &[TermId],
        atoms: &[(TermId, bool)],
    ) -> Vec<(TermId, String)> {
        let mut out: Vec<(TermId, String)> = Vec::new();
        for &var in free.iter().take(MAX_W7_VARS) {
            for len in self.w7_coupling_lengths(var, atoms) {
                let mut probe: HashMap<TermId, String> = HashMap::default();
                probe.insert(var, "a".repeat(len));
                let model = super::strings_w4::w4_trial_model(&probe);
                w4_memo_reset();
                let mut pairs: Vec<(usize, usize, bool)> = Vec::new();
                for &(t, pol) in atoms {
                    let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                        continue;
                    };
                    if name != "=" || args.len() != 2 {
                        continue;
                    }
                    let (Some(i), Some(j)) = (
                        self.w7_single_char_position(&model, args[0], var),
                        self.w7_single_char_position(&model, args[1], var),
                    ) else {
                        continue;
                    };
                    if i != j && i < len && j < len {
                        pairs.push((i, j, pol));
                    }
                }
                w4_memo_reset();
                if pairs.len() < 2 {
                    continue;
                }
                let mut parent: Vec<usize> = (0..len).collect();
                for &(i, j, pol) in &pairs {
                    if pol {
                        w7_union(&mut parent, i, j);
                    }
                }
                if pairs
                    .iter()
                    .any(|&(i, j, pol)| !pol && w7_find(&mut parent, i) == w7_find(&mut parent, j))
                {
                    continue; // the couplings contradict each other here.
                }
                let mut value: Vec<char> = Vec::with_capacity(len);
                let mut colour: HashMap<usize, char> = HashMap::default();
                let mut next = 0usize;
                for p in 0..len {
                    let root = w7_find(&mut parent, p);
                    let ch = match colour.get(&root) {
                        Some(&c) => c,
                        None => {
                            let c = W7_COUPLING_ALPHABET
                                .chars()
                                .nth(next % W7_COUPLING_ALPHABET.chars().count())
                                .unwrap_or('a');
                            next += 1;
                            colour.insert(root, c);
                            c
                        }
                    };
                    value.push(ch);
                }
                let text: String = value.into_iter().collect();
                if !out.iter().any(|(v, s)| *v == var && *s == text) {
                    out.push((var, text));
                }
                if out.len() >= MAX_W7_COUPLING_SEEDS {
                    return out;
                }
            }
        }
        out
    }

    /// Lengths worth probing for `var`'s coupling closure: an exact `str.len`
    /// pin when one exists, otherwise one past the largest index any coupling
    /// mentions.
    fn w7_coupling_lengths(&self, var: TermId, atoms: &[(TermId, bool)]) -> Vec<usize> {
        let mut out: Vec<usize> = Vec::new();
        let mut max_idx: usize = 0;
        for &(t, pol) in atoms {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name == "=" && args.len() == 2 && pol {
                for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                    if let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(lhs) {
                        if f == "str.len" && fargs.len() == 1 && fargs[0] == var {
                            if let TermData::Const(ay_core::term::Constant::Int(n)) =
                                self.ctx.terms.get(rhs)
                            {
                                if let Ok(v) = usize::try_from(n.clone()) {
                                    if v <= MAX_W4_LEN && !out.contains(&v) {
                                        out.push(v);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // Largest literal index of a window rooted at `var`.
            let mut stack: Vec<(TermId, usize)> = vec![(t, 0)];
            let mut budget = 256usize;
            while let Some((s, depth)) = stack.pop() {
                if depth > 32 || budget == 0 {
                    continue;
                }
                budget -= 1;
                if let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(s) {
                    if (f == "str.substr" && fargs.len() == 3 || f == "str.at" && fargs.len() == 2)
                        && self.w4_window_root(fargs[0], var, 0)
                    {
                        if let TermData::Const(ay_core::term::Constant::Int(n)) =
                            self.ctx.terms.get(fargs[1])
                        {
                            if let Ok(v) = usize::try_from(n.clone()) {
                                max_idx = max_idx.max(v);
                            }
                        }
                    }
                    for &a in fargs {
                        stack.push((a, depth + 1));
                    }
                }
            }
        }
        if max_idx > 0 && max_idx < MAX_W4_LEN && !out.contains(&(max_idx + 1)) {
            out.push(max_idx + 1);
        }
        out.truncate(MAX_W7_COUPLING_LENGTHS);
        out
    }

    /// The position of a SINGLE-CHARACTER window of `target`, resolved through
    /// [`Executor::w4_origin`] (both the `str.at` and the rewritten
    /// `(str.substr W I 1)` spellings).
    fn w7_single_char_position(
        &self,
        model: &super::super::model::Model,
        term: TermId,
        target: TermId,
    ) -> Option<usize> {
        if self.w4_eval_string(model, term)?.chars().count() != 1 {
            return None;
        }
        self.w4_origin(model, term, target, 0)
    }

    // ─────────────────── multi-atom placement search (shape B) ────────────

    /// W5's placement loop generalised to K > 1 SIMULTANEOUS placements.
    ///
    /// A bounded beam over placement depth: level 0 expands
    /// [`MAX_W7_PLACE_WIDTH`] single placements, keeps the best
    /// [`MAX_W7_PLACE_BEAM`] by violation count EVEN WHEN NONE IMPROVED (which
    /// is the whole point — a wide plateau is crossed only by a combination),
    /// and repeats to [`MAX_W7_PLACE_DEPTH`]. The result is adopted only when it
    /// STRICTLY improves on the entry plateau, so a non-improving stack of
    /// placements can never displace a better assignment.
    ///
    /// Returns `true` when `assign` ends with zero definitively-violated atoms.
    /// Decides nothing: the caller still routes the assignment through
    /// `finalize_sat_model_validation`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn w7_multi_placement_search(
        &mut self,
        var_atoms: &[(TermId, Vec<(TermId, bool)>)],
        atoms: &[(TermId, bool)],
        assign: &mut HashMap<TermId, String>,
        alphabet: &[char],
        numeric: &HashSet<TermId>,
        fresh: char,
    ) -> bool {
        let entry = self.w4_violations(atoms, assign);
        if entry == 0 {
            return true;
        }
        if entry > MAX_W7_ENTRY_VIOLATIONS {
            return false;
        }
        // Beam of (assignment, score); non-improving members are kept on
        // purpose, so a stack of placements can cross a plateau one placement
        // cannot.
        let mut beam: Vec<(HashMap<TermId, String>, usize)> = vec![(assign.clone(), entry)];
        let mut best: Option<(HashMap<TermId, String>, usize)> = None;
        for level in 0..MAX_W7_PLACE_DEPTH {
            let width = if level == 0 {
                MAX_W7_PLACE_WIDTH
            } else {
                MAX_W7_PLACE_WIDTH / 2
            };
            let mut next: Vec<(HashMap<TermId, String>, usize)> = Vec::new();
            for (base, _) in &beam {
                if self.should_abort_theory_loop() {
                    return false;
                }
                for (var, value) in self
                    .w5_placements(atoms, base, fresh)
                    .into_iter()
                    .take(width)
                {
                    if self.should_abort_theory_loop() {
                        return false;
                    }
                    let mut trial = base.clone();
                    trial.insert(var, value);
                    self.w4_synthesize(var_atoms, &mut trial, alphabet, numeric, fresh);
                    let score = self.w4_violations(atoms, &trial);
                    if score == 0 {
                        *assign = trial;
                        return true;
                    }
                    if best.as_ref().is_none_or(|(_, b)| score < *b) {
                        best = Some((trial.clone(), score));
                    }
                    next.push((trial, score));
                }
            }
            if next.is_empty() {
                break;
            }
            next.sort_by_key(|(_, s)| *s);
            next.truncate(MAX_W7_PLACE_BEAM);
            beam = next;
        }
        // Adopt only a STRICT improvement on the plateau we entered with.
        match best {
            Some((trial, score)) if score < entry => {
                *assign = trial;
                score == 0
            }
            _ => false,
        }
    }

    // ────────────────── distinct-word enumeration (shape C) ───────────────

    /// Two variables in the same regular language, coupled by a disequality and
    /// an equal-length constraint, need two DISTINCT words of that language at
    /// the SAME length. Build a length-grouped word pool per variable and emit
    /// ROTATED joint candidates, so coupled variables never receive the same
    /// word while the length group is preserved.
    fn w7_try_distinct_words(&mut self, vars: &[TermId]) -> Result<Option<SolveResult>> {
        // Only for formulas that actually ask for distinct values: without a
        // disequality the aligned candidates W6 already builds are strictly
        // cheaper and equally good.
        if !self.w7_has_string_disequality(vars) {
            return Ok(None);
        }
        let memberships = self.w7_memberships();
        if memberships.is_empty() {
            return Ok(None);
        }
        let mut pools: Vec<(TermId, Vec<String>)> = Vec::new();
        for &var in vars {
            let regexes: Vec<WeRegex> = memberships
                .iter()
                .filter(|&&(hay, _, pol)| hay == var && pol)
                .filter_map(|&(_, re, _)| self.translate_we_regex(re, 0))
                .collect();
            if regexes.is_empty() {
                continue;
            }
            let mut pool: Vec<String> = Vec::new();
            for len in 0..=MAX_W7_WORD_LEN {
                for w in find_witnesses_bounded(
                    &regexes,
                    Some(len),
                    MAX_W7_WITNESS_DEPTH,
                    MAX_W7_WORDS_PER_LEN,
                ) {
                    if !pool.contains(&w) {
                        pool.push(w);
                    }
                }
            }
            if !pool.is_empty() {
                pools.push((var, pool));
            }
        }
        if pools.len() < 2 {
            return Ok(None);
        }
        pools.sort_by_key(|(v, _)| v.index());
        let depth = pools.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
        let mut candidates: Vec<HashMap<TermId, String>> = Vec::new();
        // ROTATION: variable `i` takes pool entry `idx + i`. The pool is ordered
        // by length, so consecutive entries are usually the same length —
        // exactly the "two distinct words, same length" shape.
        for idx in 0..depth.min(MAX_W7_WORD_CANDIDATES) {
            let mut assign: HashMap<TermId, String> = HashMap::default();
            for (i, (var, pool)) in pools.iter().enumerate() {
                let pick = pool
                    .get((idx + i) % pool.len().max(1))
                    .cloned()
                    .unwrap_or_default();
                assign.insert(*var, pick);
            }
            // Variables with no membership at all: the empty string, which the
            // validation battery will accept or reject.
            for &v in vars {
                assign.entry(v).or_default();
            }
            if !candidates.iter().any(|c| w7_same(c, &assign)) {
                candidates.push(assign);
            }
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W7] distinct-word pre-pass: {} rotated candidate(s) over {} pooled var(s)",
                candidates.len(),
                pools.len()
            );
        }
        self.w4_validate_candidates(&candidates)
    }

    /// Whether some assertion forbids two of the formula's string variables
    /// from being equal.
    fn w7_has_string_disequality(&self, vars: &[TermId]) -> bool {
        let known: HashSet<TermId> = vars.iter().copied().collect();
        let mut stack: Vec<(TermId, bool, usize)> =
            self.ctx.assertions.iter().map(|&t| (t, true, 0)).collect();
        let mut budget = 4096usize;
        while let Some((t, pol, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push((*inner, !pol, depth + 1)),
                TermData::App(Symbol::Named(name), args) => {
                    if !pol
                        && name == "="
                        && args.len() == 2
                        && args.iter().all(|a| known.contains(a))
                    {
                        return true;
                    }
                    if name == "distinct"
                        && pol
                        && args.len() >= 2
                        && args.iter().all(|a| known.contains(a))
                    {
                        return true;
                    }
                    if name == "and" || name == "or" || name == "not" {
                        for &a in args {
                            stack.push((a, if name == "not" { !pol } else { pol }, depth + 1));
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// `str.in_re` atoms in the assertion set, as `(haystack, regex, polarity)`.
    fn w7_memberships(&self) -> Vec<(TermId, TermId, bool)> {
        let mut out: Vec<(TermId, TermId, bool)> = Vec::new();
        let mut stack: Vec<(TermId, bool, usize)> =
            self.ctx.assertions.iter().map(|&t| (t, true, 0)).collect();
        let mut budget = 4096usize;
        while let Some((t, pol, depth)) = stack.pop() {
            if depth > 64 || budget == 0 || out.len() >= 32 {
                continue;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push((*inner, !pol, depth + 1)),
                TermData::App(Symbol::Named(name), args) => {
                    if (name == "str.in_re" || name == "str.in.re") && args.len() == 2 {
                        out.push((args[0], args[1], pol));
                    } else if name == "and" || name == "or" || name == "not" {
                        for &a in args {
                            stack.push((a, if name == "not" { !pol } else { pol }, depth + 1));
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }
}

// ───────────────────────────── free helpers ───────────────────────────────

fn w7_same(a: &HashMap<TermId, String>, b: &HashMap<TermId, String>) -> bool {
    a.len() == b.len() && a.iter().all(|(k, v)| b.get(k) == Some(v))
}

fn w7_push_seed(assign: HashMap<TermId, String>, out: &mut Vec<HashMap<TermId, String>>) {
    if out.len() >= MAX_W7_SEEDS || out.iter().any(|c| w7_same(c, &assign)) {
        return;
    }
    out.push(assign);
}

/// `body` repeated into `fields` fields joined by `sep` (`"1:1:1"`).
pub(super) fn w7_segmented(sep: &str, body: &str, fields: usize) -> String {
    let mut out = String::new();
    for i in 0..fields {
        if i > 0 {
            out.push_str(sep);
        }
        out.push_str(body);
    }
    out
}

/// Resize the window `[origin, origin + have)` of `cur` to `want` characters,
/// padding with `fresh` or dropping from the window's tail. The text outside
/// the window is preserved, so the OTHER fields of a parse chain keep the
/// values the climb already gave them.
pub(super) fn w7_resize_window(
    cur: &[char],
    origin: usize,
    have: usize,
    want: usize,
    fresh: char,
) -> Option<Vec<char>> {
    if want > MAX_W4_LEN || origin > cur.len() || want == have {
        return None;
    }
    let end = origin.checked_add(have)?.min(cur.len());
    let mut out: Vec<char> = cur[..end].to_vec();
    if want > have {
        for _ in 0..(want - have) {
            out.push(fresh);
        }
    } else {
        let drop = have - want;
        if out.len() < drop {
            return None;
        }
        out.truncate(out.len() - drop);
    }
    out.extend_from_slice(&cur[end..]);
    (out.len() <= MAX_W4_LEN).then_some(out)
}

/// W7's sub-deadline: half of what the solve has left, capped.
fn w7_sub_deadline(outer: Option<ay_core::time::Instant>) -> Option<ay_core::time::Instant> {
    let dl = outer?;
    let now = ay_core::time::Instant::now();
    let budget = (dl.saturating_duration_since(now) / W7_BUDGET_SHARE).min(W7_MAX_BUDGET);
    now.checked_add(budget)
}

/// Union-find `find` with path compression.
fn w7_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

fn w7_union(parent: &mut [usize], a: usize, b: usize) {
    let (ra, rb) = (w7_find(parent, a), w7_find(parent, b));
    if ra != rb {
        parent[rb] = ra;
    }
}

/// Put the coupling-closure values at the FRONT of the seed list: they solve
/// every coupling at once, which is the whole point, and a per-position seed
/// would otherwise spend the budget re-discovering one coupling at a time.
fn w7_prepend_coupling_seeds(
    couplings: &[(TermId, String)],
    free: &[TermId],
    seeds: &mut Vec<HashMap<TermId, String>>,
) {
    if couplings.is_empty() {
        return;
    }
    let base = seeds.first().cloned().unwrap_or_default();
    let mut front: Vec<HashMap<TermId, String>> = Vec::new();
    for (var, text) in couplings {
        let mut assign = base.clone();
        for &v in free {
            assign.entry(v).or_default();
        }
        assign.insert(*var, text.clone());
        if !front.iter().any(|c| w7_same(c, &assign)) {
            front.push(assign);
        }
    }
    front.append(seeds);
    front.truncate(MAX_W7_SEEDS);
    *seeds = front;
}

/// A character outside the formula's constant alphabet when one exists.
fn w7_fresh_char(alphabet: &[char]) -> char {
    ('a'..='z')
        .chain('A'..='Z')
        .chain('0'..='9')
        .find(|c| !alphabet.contains(c))
        .unwrap_or('a')
}

#[cfg(test)]
#[path = "strings_w7_tests.rs"]
mod tests;
