// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Encoding dump for cross-solver comparison (#8323).
//!
//! When `AY_DUMP_ENCODING=<file>` is set, dumps all clauses present in the
//! SAT solver before the first solve call in an annotated DIMACS-like format.
//!
//! Provenance prefixes:
//!   `e` = encoding (problem clause)
//!   `b` = bound axiom
//!   `t` = theory lemma / theory conflict / theory propagation
//!   `s` = split encoding
//!   `l` = learned
//!   `i` = inprocessing
//!
//! If clause provenance tracking is not enabled (`AY_CLAUSE_PROVENANCE=1`),
//! all clauses default to the `e` (encoding) prefix.
//!
//! Format:
//! ```text
//! c AY encoding dump
//! c Format: prefix clause_id literals...
//! p cnf <nvars> <nclauses>
//! e 1 3 -7 0
//! b 2 -3 12 0
//! t 3 -5 8 -12 0
//! ```

use super::*;
use crate::clause_provenance::ClauseProvenance;
use std::io::{BufWriter, Write};

impl Solver {
    /// Check the cached `--dump-encoding=FILE` path (or the deprecated
    /// `AY_DUMP_ENCODING` env var) and dump clauses if set.
    ///
    /// Called once at the start of `init_solve`, before preprocessing or
    /// any CDCL iteration. Reads from the centralized `TraceConfig`
    /// singleton (#8506, #8834) so the env var is resolved exactly once
    /// per process.
    pub(super) fn maybe_dump_encoding(&self) {
        let Some(path) = ay_core::trace_config().dump_encoding_path.as_deref() else {
            return;
        };
        if let Err(e) = self.dump_encoding(path) {
            tracing::error!(path, %e, "failed to dump encoding");
        }
    }

    /// Dump all clauses in the clause arena to `path` in annotated DIMACS format.
    fn dump_encoding(&self, path: &str) -> std::io::Result<()> {
        let file = std::fs::File::create(path)?;
        let mut w = BufWriter::new(file);

        // Count active clauses + level-0 trail units for the header.
        let arena_clauses = self.arena.active_clause_count();
        let trail_units = self.trail.len();
        let total_clauses = arena_clauses + trail_units;

        writeln!(w, "c AY encoding dump")?;
        writeln!(w, "c Format: prefix clause_id literals...")?;
        writeln!(w, "p cnf {} {}", self.num_vars, total_clauses)?;

        let mut clause_id: u64 = 1;

        // Dump level-0 trail units as single-literal clauses.
        for &lit in &self.trail {
            let prefix = self.provenance_prefix_for_trail_unit();
            write!(w, "{prefix} {clause_id} {}", lit.to_dimacs())?;
            writeln!(w, " 0")?;
            clause_id += 1;
        }

        // Dump all active clauses from the arena.
        for offset in self.arena.active_indices() {
            let prefix = self.provenance_prefix(offset);
            write!(w, "{prefix} {clause_id}")?;
            let len = self.arena.len_of(offset);
            for i in 0..len {
                let lit = self.arena.literal(offset, i);
                write!(w, " {}", lit.to_dimacs())?;
            }
            writeln!(w, " 0")?;
            clause_id += 1;
        }

        w.flush()?;
        tracing::info!(path, total_clauses, "encoding dump written");
        Ok(())
    }

    /// Map clause provenance to the single-character DIMACS prefix.
    fn provenance_prefix(&self, arena_offset: usize) -> char {
        match self.provenance.get(arena_offset) {
            Some(ClauseProvenance::ProblemEncoding) => 'e',
            Some(ClauseProvenance::BoundAxiom) => 'b',
            Some(ClauseProvenance::TheoryConflict)
            | Some(ClauseProvenance::TheoryPropagation)
            | Some(ClauseProvenance::TheoryLemma) => 't',
            Some(ClauseProvenance::SplitEncoding) => 's',
            Some(ClauseProvenance::Learned) => 'l',
            Some(ClauseProvenance::Inprocessing) => 'i',
            None => 'e', // Default when provenance tracking is disabled.
        }
    }

    /// Prefix for trail unit literals (no arena offset to look up).
    fn provenance_prefix_for_trail_unit(&self) -> char {
        // Trail units at solve start are from encoding or BCP; default to 'e'.
        'e'
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dump_encoding_basic() {
        // Build a small formula: (1 v 2) ^ (-1 v 3) ^ (-2 v -3)
        let mut solver = Solver::new(3);
        solver.add_clause(vec![Literal::from_dimacs(1), Literal::from_dimacs(2)]);
        solver.add_clause(vec![Literal::from_dimacs(-1), Literal::from_dimacs(3)]);
        solver.add_clause(vec![Literal::from_dimacs(-2), Literal::from_dimacs(-3)]);

        let dir = std::env::temp_dir();
        let path = dir.join("ay_dump_test_basic.cnf");
        let path_str = path.to_str().expect("temp path should be valid UTF-8");

        solver.dump_encoding(path_str).expect("dump should succeed");

        let contents = std::fs::read_to_string(&path).expect("should read dump file");
        // Verify header
        assert!(contents.contains("c AY encoding dump"));
        assert!(contents.contains("p cnf 3 3"));
        // Verify clauses are present (with 'e' prefix since no provenance tracking)
        assert!(contents.contains("e 1"));
        assert!(contents.contains("e 2"));
        assert!(contents.contains("e 3"));
        // Every clause line ends with " 0"
        for line in contents.lines() {
            if line.starts_with('e') {
                assert!(
                    line.ends_with(" 0"),
                    "clause line should end with ' 0': {line}"
                );
            }
        }

        // Clean up
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_dump_encoding_with_unit_propagation() {
        // Build a formula with a unit clause that gets propagated at level 0.
        // (1) ^ (1 v 2) ^ (-1 v 3)
        let mut solver = Solver::new(3);
        solver.add_clause(vec![Literal::from_dimacs(1)]);
        solver.add_clause(vec![Literal::from_dimacs(1), Literal::from_dimacs(2)]);
        solver.add_clause(vec![Literal::from_dimacs(-1), Literal::from_dimacs(3)]);

        let dir = std::env::temp_dir();
        let path = dir.join("ay_dump_test_unit.cnf");
        let path_str = path.to_str().expect("temp path should be valid UTF-8");

        solver.dump_encoding(path_str).expect("dump should succeed");

        let contents = std::fs::read_to_string(&path).expect("should read dump file");
        // The unit clause is in the trail, plus 2 arena clauses
        // (unit clauses may or may not be in the arena depending on add_clause impl)
        assert!(contents.contains("c AY encoding dump"));
        assert!(contents.contains("p cnf"));
        // There should be at least 3 clause lines
        let clause_lines: Vec<&str> = contents
            .lines()
            .filter(|l| !l.starts_with('c') && !l.starts_with('p'))
            .collect();
        assert!(
            clause_lines.len() >= 3,
            "expected at least 3 clauses, got {}",
            clause_lines.len()
        );

        // Clean up
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_dump_encoding_empty_formula() {
        let solver = Solver::new(5);

        let dir = std::env::temp_dir();
        let path = dir.join("ay_dump_test_empty.cnf");
        let path_str = path.to_str().expect("temp path should be valid UTF-8");

        solver.dump_encoding(path_str).expect("dump should succeed");

        let contents = std::fs::read_to_string(&path).expect("should read dump file");
        assert!(contents.contains("p cnf 5 0"));

        // Clean up
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_provenance_prefix_default() {
        let solver = Solver::new(3);
        // With provenance disabled, all clauses get 'e' prefix
        assert_eq!(solver.provenance_prefix(0), 'e');
        assert_eq!(solver.provenance_prefix(999), 'e');
    }
}
