// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessed-CNF dump: run preprocessing to its initial fixpoint and write
//! the residual formula back out as plain DIMACS.
//!
//! The file this writes is a *formula*, not a proof and not a model — the only
//! contract it carries is EQUISATISFIABILITY with the formula that was loaded
//! into the solver.
//!
//! Distinct from `solver/dump.rs` (`--dump-encoding`), which dumps the
//! PRE-preprocessing formula in an annotated, non-DIMACS format for human
//! comparison against another solver's encoding. See that file's header for
//! the full comparison and for why its `active_indices()`/internal-literal
//! choices cannot simply be reused after preprocessing has run.
//!
//! # What is written
//!
//! * every level-0 trail assignment, as a unit clause;
//! * every *live* arena clause (`ClauseArena::live_indices`), verbatim.
//!
//! `live_indices` — not `active_indices` — is the formula-semantics iterator:
//! `active_indices` also yields garbage-kept husks, which are logically
//! deleted clauses whose literal data is retained for reason-pointer windows.
//! Emitting a husk would add a constraint the solver no longer believes and
//! can turn SAT into UNSAT.
//!
//! Redundant (learned/derived) clauses present at the fixpoint are written
//! too. They are implied by the irredundant part, so they cannot change the
//! verdict; they only save the consuming solver the work of rederiving them.
//!
//! # Variable space
//!
//! Literals are written in the solver's EXTERNAL variable space, obtained via
//! `externalize()` (the `i2e` map). External indices are assigned at variable
//! creation and never move, so for a formula loaded straight from a DIMACS
//! file the emitted numbering IS the original file's numbering — even if
//! variable compaction renumbered the internal space underneath.
//!
//! Two consequences, both stated in the emitted header:
//!
//! * Variables eliminated by BVE or substituted by decompose/congruence occur
//!   in no emitted clause. They are simply absent, which is sound for
//!   satisfiability but means a model of the dump is NOT a model of the
//!   source formula: recovering one needs AY's reconstruction (extension)
//!   stack, which this file does not carry.
//! * Extension variables introduced by AY (factoring, SBVA, gate definitions)
//!   are emitted with their own external indices, above the source formula's
//!   maximum.
//!
//! # The header keeps the source `maxvar` — deliberately
//!
//! The `p cnf` line declares `max(source maxvar, largest emitted var)`, NOT
//! the number of variables that survived. Eliminated variables leave HOLES in
//! the numbering and those holes are load-bearing: they are what makes DRAT
//! composition work.
//!
//! If AY emits a DRAT prefix `P1` carrying a checker from `F` to `F'`, and a
//! downstream solver emits `P2` refuting `F'`, then `cat P1 P2` is a single
//! certificate for `F` — but only while both proofs speak the same variable
//! space. Renumbering `F'` to close the holes would express `P2` in a space
//! `P1` never mentions and make the concatenation meaningless, which would
//! restrict the whole composition route to SAT instances. DIMACS permits
//! unused indices; the wasted array space downstream is worth a checkable
//! certificate.

use super::config_preprocess_cleanup::PreprocessOutcome;
use super::*;
use std::io::{BufWriter, Write};
use std::path::Path;

/// What preprocessing concluded before/while producing the dump.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DumpCnfVerdict {
    /// A residual formula was written; the instance is still open.
    Dumped,
    /// Preprocessing derived the empty clause. No file was written.
    Unsat,
    /// Preprocessing fully solved the instance (nothing left to constrain).
    /// The file is still written, and is trivially satisfiable.
    Sat,
}

/// Accounting for one preprocessed-CNF dump.
#[derive(Debug, Clone)]
pub struct DumpCnfReport {
    /// Result of preprocessing before the CNF was written.
    pub verdict: DumpCnfVerdict,
    /// `maxvar` as written in the `p cnf` header. This is
    /// `max(source maxvar, largest emitted external var)` — the SOURCE
    /// variable space with holes, never a compacted renumbering.
    pub max_var: usize,
    /// `nclauses` as written in the header. Equals the number of clause lines
    /// actually emitted — counted, never estimated.
    pub num_clauses: usize,
    /// Unit clauses emitted from the level-0 trail.
    pub num_units: usize,
    /// Arena clauses emitted.
    pub num_arena_clauses: usize,
    /// Of `num_arena_clauses`, how many carried the redundant/learned flag.
    pub num_redundant: usize,
    /// Source formula variable count (`user_num_vars` at load time).
    pub source_num_vars: usize,
    /// Source formula clause count as loaded.
    pub source_num_clauses: usize,
    /// Variables eliminated (BVE) or substituted (decompose/congruence).
    pub removed_vars: usize,
    /// Variables fixed at level 0.
    pub fixed_vars: usize,
    /// Level-0 trail entries skipped because their variable was removed.
    pub skipped_removed_units: usize,
    /// Clauses emitted that still mention a removed variable. MUST be 0 —
    /// `finalize_preprocess_clause_cleanup` makes that an invariant. A
    /// non-zero value is a correctness defect in the dump's input, and is
    /// reported both here and as a `c WARNING` line in the file.
    pub leaked_removed_var_clauses: usize,
    /// Wall time spent inside preprocessing, milliseconds.
    pub preprocess_ms: u128,
}

/// Result of lifting an assignment over the dumped formula back to the source.
#[derive(Debug, Clone)]
pub struct ExtendModelReport {
    /// Model over `1..=source maxvar`, as DIMACS literals.
    pub model: Vec<i32>,
    /// Reconstruction stack depth that was replayed.
    pub reconstruction_steps: usize,
    /// Literals taken from the supplied assignment.
    pub assigned_from_input: usize,
    /// Supplied literals naming a variable outside the solver's space.
    pub out_of_range_literals: usize,
    /// Whether the extended model satisfies EVERY original clause. This is
    /// the gate: `false` means the composition produced a wrong answer.
    pub verified_against_source: bool,
}

impl DumpCnfReport {
    fn empty(verdict: DumpCnfVerdict, source_num_vars: usize, source_num_clauses: usize) -> Self {
        Self {
            verdict,
            max_var: 0,
            num_clauses: 0,
            num_units: 0,
            num_arena_clauses: 0,
            num_redundant: 0,
            source_num_vars,
            source_num_clauses,
            removed_vars: 0,
            fixed_vars: 0,
            skipped_removed_units: 0,
            leaked_removed_var_clauses: 0,
            preprocess_ms: 0,
        }
    }
}

impl Solver {
    /// Run preprocessing to its normal initial fixpoint, then write the
    /// residual formula to `path` as DIMACS.
    ///
    /// This deliberately runs only the *simplification* prefix of a solve: the
    /// level-0 unit/BCP initialization plus the initial preprocessing phase.
    /// The startup search probes (lucky phases, the GF(p) linear probe, the
    /// independent-support enumeration) are skipped — they are solvers, not
    /// simplifiers, and a dump should not be able to succeed by accident.
    ///
    /// Never writes a file for an UNSAT verdict: a formula file cannot
    /// represent "already refuted" and a bogus one is worse than none.
    pub fn preprocess_and_dump_cnf(&mut self, path: &Path) -> std::io::Result<DumpCnfReport> {
        let source_num_vars = self.user_num_vars;
        let source_num_clauses = self.arena.active_clause_count();

        let (verdict, preprocess_ms) = self.preprocess_for_dump();
        if verdict == DumpCnfVerdict::Unsat {
            return Ok(DumpCnfReport::empty(
                DumpCnfVerdict::Unsat,
                source_num_vars,
                source_num_clauses,
            ));
        }
        let solved_sat = verdict == DumpCnfVerdict::Sat;

        let mut report = self.write_preprocessed_dimacs(path, source_num_vars)?;
        report.source_num_vars = source_num_vars;
        report.source_num_clauses = source_num_clauses;
        report.preprocess_ms = preprocess_ms;
        if solved_sat || report.num_clauses == 0 {
            report.verdict = DumpCnfVerdict::Sat;
        }

        // The dump-and-exit path skips the normal solve epilogue, so nothing
        // else will push the preprocessing DRAT prefix out of the writer's
        // buffer. Without this the tail of P1 is lost and `cat P1 P2` cannot
        // verify.
        if let Some(pm) = self.proof_manager.as_mut() {
            pm.flush()?;
        }
        Ok(report)
    }

    /// Drive the solver to the state a `--dump-cnf` writes from: level-0
    /// units, watch setup, initial BCP, then the initial preprocessing phase
    /// and its mandatory cleanup.
    ///
    /// Deliberately runs only the *simplification* prefix of a solve. The
    /// startup search probes (lucky phases, GF(p) linear probe,
    /// independent-support enumeration) are skipped — they are solvers, not
    /// simplifiers, and a preprocessing dump should not succeed by accident.
    ///
    /// Returns the verdict and the preprocessing wall time in milliseconds.
    /// `Sat` means preprocessing left nothing to decide; `Unsat` means the
    /// empty clause was derived.
    pub fn preprocess_for_dump(&mut self) -> (DumpCnfVerdict, u128) {
        if self.has_empty_clause {
            return (DumpCnfVerdict::Unsat, 0);
        }

        if let Some(result) = self.init_solve() {
            return match result {
                SatResult::Unsat(_) => (DumpCnfVerdict::Unsat, 0),
                // Empty arena: everything is already satisfied.
                _ => (DumpCnfVerdict::Sat, 0),
            };
        }

        if !self.cold.preprocess_enabled {
            return (DumpCnfVerdict::Dumped, 0);
        }

        let t0 = ay_core::time::Instant::now();
        let never_stop = || false;
        let outcome = self.preprocess_interruptible(&never_stop);
        let cleanup_unsat = self.finish_initial_preprocessing();
        let preprocess_ms = t0.elapsed().as_millis();

        match outcome {
            PreprocessOutcome::Unsat => (DumpCnfVerdict::Unsat, preprocess_ms),
            // A cooperative stop still leaves a consistent residual formula
            // (cleanup runs unconditionally); it is simply a shallower
            // fixpoint, and is dumpable.
            PreprocessOutcome::Stopped(_) | PreprocessOutcome::Complete => {
                if cleanup_unsat || self.has_empty_clause {
                    (DumpCnfVerdict::Unsat, preprocess_ms)
                } else {
                    (DumpCnfVerdict::Dumped, preprocess_ms)
                }
            }
        }
    }

    /// Number of live clauses currently in the arena.
    ///
    /// A dump caller must check this BEFORE preprocessing: an arena that is
    /// already empty means the formula was routed somewhere the arena cannot
    /// see, and anything dumped from it would be a strict weakening.
    #[must_use]
    pub fn live_clause_count(&self) -> usize {
        self.arena.active_clause_count()
    }

    /// Number of reconstruction (witness/extension) steps recorded so far.
    ///
    /// Non-zero means a model of the dumped formula is NOT a model of the
    /// source formula until `extend_dumped_model` replays these steps.
    #[must_use]
    pub fn reconstruction_step_count(&self) -> usize {
        self.inproc.reconstruction.len()
    }

    /// Extend an assignment over the dumped formula into a model of the
    /// SOURCE formula.
    ///
    /// `assignment` is a list of DIMACS literals in the dump's variable space
    /// (which is the source variable space — see the module docs). Variables
    /// the assignment omits keep their preprocessing-time level-0 value, or
    /// `false`.
    ///
    /// This replays AY's reconstruction (extension) stack — the same stack
    /// `finalize_sat_model` uses — and then checks the result against the
    /// immutable original-clause ledger. The check is the point: it is what
    /// distinguishes "the composition works" from "the composition produced a
    /// plausible-looking wrong answer".
    ///
    /// Returns the model as DIMACS literals over `1..=source maxvar`, plus
    /// whether it satisfies every original clause.
    pub fn extend_dumped_model(&mut self, assignment: &[i32]) -> ExtendModelReport {
        let ext_num_vars = self.cold.e2i.len();

        // Seed exactly as `finalize_sat_model` does: internal level-0 values
        // through `e2i`, with compacted-away eliminated variables taking their
        // saved external-space value.
        let mut ext_model = vec![false; ext_num_vars];
        for (ext_var, val) in ext_model.iter_mut().enumerate() {
            let int_var = self.cold.e2i[ext_var];
            if int_var == compact::UNMAPPED {
                if ext_var < self.cold.eliminated_ext_vals.len() {
                    *val = self.cold.eliminated_ext_vals[ext_var];
                }
                continue;
            }
            let int_var = int_var as usize;
            if int_var * 2 < self.vals.len() {
                *val = self.vals[int_var * 2] > 0;
            }
        }

        // Overlay the downstream solver's assignment.
        let mut applied = 0usize;
        let mut out_of_range = 0usize;
        for &lit in assignment {
            if lit == 0 {
                continue;
            }
            let ext_var = lit.unsigned_abs() as usize - 1;
            if ext_var >= ext_num_vars {
                out_of_range += 1;
                continue;
            }
            ext_model[ext_var] = lit > 0;
            applied += 1;
        }

        let steps = self.inproc.reconstruction.len();
        self.inproc.reconstruction.reconstruct(&mut ext_model);

        let verified = self.verify_external_model(&ext_model);

        let source_num_vars = self.user_num_vars.min(ext_num_vars);
        let model: Vec<i32> = (0..source_num_vars)
            .map(|v| {
                let lit = v as i32 + 1;
                if ext_model[v] {
                    lit
                } else {
                    -lit
                }
            })
            .collect();

        ExtendModelReport {
            model,
            reconstruction_steps: steps,
            assigned_from_input: applied,
            out_of_range_literals: out_of_range,
            verified_against_source: verified,
        }
    }

    /// Emit the live formula. Two passes: the first counts (so the header is
    /// measured, not guessed), the second writes.
    fn write_preprocessed_dimacs(
        &self,
        path: &Path,
        source_num_vars: usize,
    ) -> std::io::Result<DumpCnfReport> {
        let removed_vars = self.var_lifecycle.count_removed();
        let fixed_vars = self.count_fixed_vars();

        // ── Pass 1: measure ────────────────────────────────────────────────
        // Seeded with the SOURCE variable count, not 0: eliminated variables
        // must leave holes in the numbering so a DRAT prefix emitted by
        // preprocessing and a DRAT suffix emitted by the downstream solver
        // still speak the same variable space and can be concatenated.
        let mut max_var = source_num_vars;
        let mut num_units = 0usize;
        let mut skipped_removed_units = 0usize;
        for &lit in &self.trail {
            if self.var_lifecycle.is_removed(lit.variable().index()) {
                // The variable occurs in no live clause, so its level-0 value
                // is irrelevant to the residual formula's satisfiability.
                // Omitting it is strictly safe; emitting it would pin a
                // variable whose defining clauses are gone.
                skipped_removed_units += 1;
                continue;
            }
            max_var = max_var.max(self.externalize(lit).variable().index() + 1);
            num_units += 1;
        }

        let mut num_arena_clauses = 0usize;
        let mut num_redundant = 0usize;
        let mut leaked_removed_var_clauses = 0usize;
        for idx in self.arena.live_indices() {
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            let mut leaked = false;
            for &lit in lits {
                let vi = lit.variable().index();
                if vi < self.var_lifecycle.len() && self.var_lifecycle.is_removed(vi) {
                    leaked = true;
                }
                max_var = max_var.max(self.externalize(lit).variable().index() + 1);
            }
            if leaked {
                leaked_removed_var_clauses += 1;
            }
            if self.arena.is_learned(idx) {
                num_redundant += 1;
            }
            num_arena_clauses += 1;
        }

        let num_clauses = num_units + num_arena_clauses;

        // ── Pass 2: write ──────────────────────────────────────────────────
        let file = std::fs::File::create(path)?;
        let mut w = BufWriter::with_capacity(1 << 20, file);

        writeln!(w, "c AY preprocessed CNF dump")?;
        writeln!(
            w,
            "c contract: EQUISATISFIABLE with the source formula (not model-equivalent)"
        )?;
        writeln!(
            w,
            "c variable space: source DIMACS numbering (AY external indices), NOT renumbered"
        )?;
        writeln!(
            w,
            "c   eliminated/substituted variables occur in NO clause below; their"
        )?;
        writeln!(
            w,
            "c   indices are left as holes so a preprocessing DRAT prefix and a"
        )?;
        writeln!(
            w,
            "c   downstream DRAT suffix remain concatenable over one variable space."
        )?;
        writeln!(
            w,
            "c   Recovering a model of the source needs AY's reconstruction stack"
        )?;
        writeln!(
            w,
            "c   (replay it with `ay solve --extend-model <assignment> <source.cnf>`)."
        )?;
        writeln!(
            w,
            "c   AY extension variables (factoring/SBVA/definitions) are numbered"
        )?;
        writeln!(w, "c   above the source formula's maximum.")?;
        writeln!(
            w,
            "c residual: units={num_units} arena={num_arena_clauses} \
             redundant={num_redundant} removed_vars={removed_vars} fixed_vars={fixed_vars}"
        )?;
        if skipped_removed_units > 0 {
            writeln!(
                w,
                "c note: {skipped_removed_units} level-0 assignment(s) of removed variables omitted"
            )?;
        }
        if leaked_removed_var_clauses > 0 {
            writeln!(
                w,
                "c WARNING: {leaked_removed_var_clauses} emitted clause(s) still mention a \
                 removed variable; this violates a preprocessing invariant"
            )?;
        }
        writeln!(w, "p cnf {max_var} {num_clauses}")?;

        let mut written = 0usize;
        for &lit in &self.trail {
            if self.var_lifecycle.is_removed(lit.variable().index()) {
                continue;
            }
            writeln!(w, "{} 0", self.externalize(lit).to_dimacs())?;
            written += 1;
        }
        for idx in self.arena.live_indices() {
            let lits = self.arena.literals(idx);
            if lits.is_empty() {
                continue;
            }
            for &lit in lits {
                write!(w, "{} ", self.externalize(lit).to_dimacs())?;
            }
            writeln!(w, "0")?;
            written += 1;
        }
        w.flush()?;

        assert_eq!(
            written, num_clauses,
            "BUG: preprocessed CNF dump wrote {written} clauses but declared {num_clauses}",
        );

        if leaked_removed_var_clauses > 0 {
            tracing::error!(
                leaked_removed_var_clauses,
                "preprocessed CNF dump emitted clauses mentioning removed variables"
            );
        }

        Ok(DumpCnfReport {
            verdict: DumpCnfVerdict::Dumped,
            max_var,
            num_clauses,
            num_units,
            num_arena_clauses,
            num_redundant,
            source_num_vars: 0,
            source_num_clauses: 0,
            removed_vars,
            fixed_vars,
            skipped_removed_units,
            leaked_removed_var_clauses,
            preprocess_ms: 0,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp(name: &str) -> std::path::PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!("ay_dump_cnf_{name}_{}.cnf", std::process::id()));
        p
    }

    /// Every emitted line must parse, the header counts must match the body,
    /// and no eliminated variable may appear.
    fn parse_dump(text: &str) -> (usize, usize, Vec<Vec<i32>>) {
        let mut header = None;
        let mut clauses = Vec::new();
        for line in text.lines() {
            if line.starts_with('c') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("p cnf ") {
                let mut it = rest.split_whitespace();
                let v: usize = it.next().unwrap().parse().unwrap();
                let c: usize = it.next().unwrap().parse().unwrap();
                header = Some((v, c));
                continue;
            }
            let lits: Vec<i32> = line
                .split_whitespace()
                .map(|t| t.parse::<i32>().unwrap())
                .collect();
            assert_eq!(lits.last(), Some(&0), "clause line must end in 0: {line}");
            clauses.push(lits[..lits.len() - 1].to_vec());
        }
        let (v, c) = header.expect("dump must have a p-line");
        assert_eq!(c, clauses.len(), "header count must match emitted clauses");
        for cl in &clauses {
            for &l in cl {
                assert!(
                    l.unsigned_abs() as usize <= v,
                    "literal {l} exceeds header maxvar {v}"
                );
            }
        }
        (v, c, clauses)
    }

    #[test]
    fn dump_is_equisatisfiable_on_a_satisfiable_formula() {
        // (1 v 2) & (-1 v 3) & (-2 v -3) & (2 v 3)
        let mut s = Solver::new(3);
        for c in [[1, 2], [-1, 3], [-2, -3], [2, 3]] {
            s.add_clause(c.iter().map(|&l| Literal::from_dimacs(l)).collect());
        }
        let path = tmp("sat");
        let report = s.preprocess_and_dump_cnf(&path).expect("dump");
        assert_ne!(report.verdict, DumpCnfVerdict::Unsat);
        assert_eq!(report.leaked_removed_var_clauses, 0);
        let text = std::fs::read_to_string(&path).unwrap();
        let (_, _, clauses) = parse_dump(&text);
        // Brute force: the residual must be satisfiable.
        let nv = report.max_var;
        let sat = (0u32..(1u32 << nv)).any(|mask| {
            clauses.iter().all(|cl| {
                cl.iter().any(|&l| {
                    let v = l.unsigned_abs() as usize - 1;
                    let val = mask >> v & 1 == 1;
                    if l > 0 {
                        val
                    } else {
                        !val
                    }
                })
            })
        });
        assert!(sat, "dumped residual must stay satisfiable");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn unsat_preprocessing_writes_no_file() {
        // (1) & (-1)
        let mut s = Solver::new(1);
        s.add_clause(vec![Literal::from_dimacs(1)]);
        s.add_clause(vec![Literal::from_dimacs(-1)]);
        let path = tmp("unsat");
        let _ = std::fs::remove_file(&path);
        let report = s.preprocess_and_dump_cnf(&path).expect("dump");
        assert_eq!(report.verdict, DumpCnfVerdict::Unsat);
        assert!(
            !path.exists(),
            "no formula file may be written for an UNSAT verdict"
        );
    }

    #[test]
    fn root_units_are_emitted_as_unit_clauses() {
        // (1) forces x1; (−1 v 2) then forces x2.
        let mut s = Solver::new(3);
        s.add_clause(vec![Literal::from_dimacs(1)]);
        s.add_clause(vec![Literal::from_dimacs(-1), Literal::from_dimacs(2)]);
        s.add_clause(vec![
            Literal::from_dimacs(-2),
            Literal::from_dimacs(3),
            Literal::from_dimacs(1),
        ]);
        let path = tmp("units");
        let report = s.preprocess_and_dump_cnf(&path).expect("dump");
        let text = std::fs::read_to_string(&path).unwrap();
        let (_, _, clauses) = parse_dump(&text);
        assert_eq!(report.leaked_removed_var_clauses, 0);
        let units: Vec<i32> = clauses
            .iter()
            .filter(|c| c.len() == 1)
            .map(|c| c[0])
            .collect();
        assert!(
            units.contains(&1),
            "root unit x1 must be emitted: {units:?}"
        );
        assert!(
            units.contains(&2),
            "root unit x2 must be emitted: {units:?}"
        );
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn header_count_equals_emitted_line_count() {
        let mut s = Solver::new(6);
        for c in [
            [1, 2, 3],
            [-1, -2, 4],
            [2, -3, 5],
            [-4, -5, 6],
            [1, -6, 3],
            [-2, 4, -5],
        ] {
            s.add_clause(c.iter().map(|&l| Literal::from_dimacs(l)).collect());
        }
        let path = tmp("counts");
        let report = s.preprocess_and_dump_cnf(&path).expect("dump");
        let text = std::fs::read_to_string(&path).unwrap();
        let body = text
            .lines()
            .filter(|l| !l.starts_with('c') && !l.starts_with("p cnf"))
            .count();
        assert_eq!(report.num_clauses, body);
        parse_dump(&text);
        let _ = std::fs::remove_file(&path);
    }
}
