// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quick CaDiCaL `elimfast.cpp`-style candidate filtering for a separate BVE pre-pass.
//!
//! CaDiCaL's `elimfast` runs at startup with much tighter limits than the main
//! BVE pass (`fastelimocclim`, `fastelimclslim`, `fastelimbound`). This module
//! provides a candidate selection pass that identifies variables cheap enough to
//! eliminate in an initial quick sweep before the full BVE pipeline fires.
//!
//! Reference: `reference/cadical/src/elimfast.cpp:15-44` (flush_elimfast_occs),
//!            `reference/cadical/src/elimfast.cpp:55-133` (bounded resolvent check)

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

use super::BVE;

/// Maximum occurrences per polarity for the quick elimination pre-pass.
/// CaDiCaL `fastelimocclim=100` (options.hpp). We use a tighter default (5)
/// to catch only the easiest eliminations at near-zero cost, leaving harder
/// variables to the full BVE pass with occurrence limit 500.
pub(crate) const QUICK_ELIM_OCC_LIMIT: usize = 5;

/// Maximum clause size (in literals) considered by the quick elimination pre-pass.
/// CaDiCaL `fastelimclslim=100` (options.hpp). We use a tighter default (20)
/// so the quick pass avoids large-clause resolution products.
pub(crate) const QUICK_ELIM_CLS_LIMIT: usize = 20;

/// Maximum non-tautological resolvents allowed by the quick elimination pre-pass.
/// CaDiCaL `fastelimbound=8` (options.hpp:128). Used as the growth bound for
/// the quick BVE pass.
pub(crate) const QUICK_ELIM_BOUND: usize = 8;

impl BVE {
    /// Collect variables eligible for the quick elimination pre-pass.
    ///
    /// Filters variables by tight occurrence and clause-size limits, returning
    /// them sorted by ascending total occurrence count (cheapest first).
    /// The caller then runs the standard BVE elimination loop over only these
    /// candidates with `QUICK_ELIM_BOUND` as the growth bound.
    ///
    /// CaDiCaL `elimfast.cpp:186-255`: flush occ lists, check limits,
    /// sort by occurrence count, attempt elimination.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn quick_eliminate_candidates(
        &self,
        arena: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
    ) -> Vec<Variable> {
        let mut candidates: Vec<(Variable, usize)> = Vec::new();

        for var_idx in 0..self.num_vars {
            // Skip eliminated variables.
            if self.eliminated[var_idx] {
                continue;
            }

            // Skip assigned variables (vals is indexed by literal index = var_idx * 2).
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }

            // Skip frozen variables.
            if frozen.get(var_idx).copied().unwrap_or(0) > 0 {
                continue;
            }

            let var = Variable(var_idx as u32);
            let pos_lit = Literal::positive(var);
            let neg_lit = Literal::negative(var);
            let pos_count = self.occ.count(pos_lit);
            let neg_count = self.occ.count(neg_lit);

            // CaDiCaL elimfast.cpp:198-210: skip if either polarity exceeds limit.
            if pos_count > QUICK_ELIM_OCC_LIMIT || neg_count > QUICK_ELIM_OCC_LIMIT {
                continue;
            }

            // Skip pure literals (one side empty) — these are handled by
            // level-0 propagation, not BVE.
            if pos_count == 0 && neg_count == 0 {
                continue;
            }

            // CaDiCaL elimfast.cpp:28-30: skip if any clause exceeds size limit.
            let pos_occs = self.occ.get(pos_lit);
            let neg_occs = self.occ.get(neg_lit);
            let has_oversized = pos_occs
                .iter()
                .chain(neg_occs.iter())
                .any(|&idx| arena.len_of(idx) > QUICK_ELIM_CLS_LIMIT);
            if has_oversized {
                continue;
            }

            candidates.push((var, pos_count + neg_count));
        }

        // Sort cheapest first (fewest total occurrences).
        candidates.sort_unstable_by_key(|&(var, total)| (total, var));
        candidates.into_iter().map(|(var, _)| var).collect()
    }
}
