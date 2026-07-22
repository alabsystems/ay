// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause rewriting using SCC representative mapping.
//!
//! After SCC decomposition identifies equivalent literals, this module
//! computes a pure rewrite plan (no side effects) that the solver
//! integration code applies through the shared mutation protocol.
//!
//! Reference: CaDiCaL `decompose.cpp:436+`

use crate::clause_arena::ClauseArena;
use crate::lit_marks::{ClauseRewriteOutcome, LitMarks};
use crate::literal::Literal;

/// Compute a rewrite plan for all clauses using the representative mapping.
///
/// This function is **read-only** with respect to `clause_db` — it returns a
/// `RewriteResult` containing all planned mutations as `ClauseMutation` entries.
/// The caller applies these mutations through the shared mutation protocol
/// in the solver integration code.
///
/// # Design (#3440)
///
/// Previously, this function took `&mut ClauseArena` and directly called
/// `clause_db.delete()` and `clause_db.replace()`. That bypassed the shared
/// mutation helpers in `mutate.rs`, creating a shadow mutation path. Now all
/// clause mutations are deferred to the caller, ensuring uniform watch,
/// proof, and diagnostic handling.
pub(crate) fn rewrite_clauses(
    clause_db: &ClauseArena,
    reprs: &[Literal],
    vals: &[i8],
) -> RewriteResult {
    // CaDiCaL decompose.cpp:436: reprs must cover all literal indices
    debug_assert!(
        !reprs.is_empty(),
        "BUG: rewrite_clauses called with empty reprs"
    );
    let mut result = RewriteResult::default();
    let num_vars = reprs.len().div_ceil(2);
    let mut marks = LitMarks::new(num_vars);
    let mut scratch = Vec::new();

    for idx in clause_db.indices() {
        if clause_db.is_empty_clause(idx) || clause_db.is_garbage(idx) {
            continue;
        }

        let lits = clause_db.literals(idx);

        // Quick check: does any literal change?
        let mut needs_rewrite = false;
        for &lit in lits {
            let li = lit.index();
            if li < reprs.len() && reprs[li] != lit {
                needs_rewrite = true;
                break;
            }
        }
        if !needs_rewrite {
            continue;
        }

        let old_lits = clause_db.literals(idx);

        match marks.rewrite_clause(lits, reprs, vals, &mut scratch) {
            ClauseRewriteOutcome::Satisfied | ClauseRewriteOutcome::Tautology => {
                result.actions.push(ClauseMutation::Deleted {
                    clause_idx: idx,
                    old: old_lits.to_vec(),
                });
                result.removed += 1;
            }
            ClauseRewriteOutcome::Empty => {
                result.is_unsat = true;
                return result;
            }
            ClauseRewriteOutcome::Unit(unit) => {
                result.new_units.push(unit);
                result.actions.push(ClauseMutation::Unit {
                    clause_idx: idx,
                    unit,
                    old: old_lits.to_vec(),
                });
                result.removed += 1;
            }
            ClauseRewriteOutcome::Changed => {
                if scratch.len() == 2 {
                    result.new_binary = true;
                }
                if scratch.len() < old_lits.len() {
                    result.shortened += 1;
                }
                result.actions.push(ClauseMutation::Replaced {
                    clause_idx: idx,
                    old: old_lits.to_vec(),
                    new: scratch.clone(),
                });
            }
            ClauseRewriteOutcome::Unchanged => {}
        }
    }

    result
}

/// A clause mutation recorded during rewriting, for DRAT/LRAT proof logging.
///
/// Each variant carries `clause_idx` — the clause database index at the time
/// of mutation. This enables the solver to look up the real clause ID for LRAT
/// proof records (DRAT only needs literal content, LRAT needs numeric IDs).
#[derive(Debug)]
pub(crate) enum ClauseMutation {
    /// Clause was deleted. Old literals stored for DRAT `d` record.
    Deleted {
        clause_idx: usize,
        old: Vec<Literal>,
    },
    /// Clause was replaced. Old and new literals stored for DRAT `a`+`d` records.
    Replaced {
        clause_idx: usize,
        old: Vec<Literal>,
        new: Vec<Literal>,
    },
    /// Clause was reduced to a unit. DRAT order: add unit THEN delete old.
    /// The unit must be RUP from the formula including the old clause.
    Unit {
        clause_idx: usize,
        unit: Literal,
        old: Vec<Literal>,
    },
}

/// Result of clause rewriting — a pure plan with no side effects.
///
/// Contains all planned mutations as `ClauseMutation` entries. The caller
/// applies these through the shared mutation protocol (#3440).
#[derive(Debug, Default)]
pub(crate) struct RewriteResult {
    /// Number of clauses removed (satisfied, tautological, or became unit).
    pub removed: u32,
    /// Number of clauses shortened.
    pub shortened: u32,
    /// New unit literals to propagate.
    pub new_units: Vec<Literal>,
    /// Whether a new binary clause was produced.
    pub new_binary: bool,
    /// Whether an empty clause was found (UNSAT).
    pub is_unsat: bool,
    /// All clause mutations to apply. The caller is responsible for
    /// applying these and emitting proof records in the correct two-phase
    /// order (all adds first, then all deletes) for DRAT/LRAT correctness.
    pub actions: Vec<ClauseMutation>,
}
