// Copyright 2026 Andrew Yates
// Precise RUP dependency tracking via MARK-based conflict analysis.
// Used by the backward checker to identify exactly which clauses are
// needed in the resolution proof chain for an ACTIVE clause's RUP check.
// Algorithm from drat-trim (Heule & Wetzler 2014), analyze() at
// drat-trim.c:164-184.
//
// Clause reduction (drat-trim.c:174-179): after conflict analysis, literals
// from the checked clause that were ASSUMED but never reached via MARK are
// unused — they can be removed. This produces smaller clauses, reducing BCP
// work in subsequent backward steps.

use crate::literal::Literal;

use super::DratChecker;

/// Result of a RUP check with dependency tracking and clause reduction info.
pub(super) struct RupDepsResult {
    pub(super) is_rup: bool,
    pub(super) deps: Vec<usize>,
    /// Indices (into the original clause) of literals that were ASSUMED but
    /// never participated in the conflict derivation. These can be removed
    /// from the clause in the arena to reduce future BCP work.
    /// drat-trim.c:174-179.
    pub(super) reducible_positions: Vec<usize>,
}

impl DratChecker {
    /// Like `check_rup`, but on success also collects the set of clause
    /// indices in the resolution proof chain (the reason clauses needed to
    /// derive the conflict). This runs the MARK-based analysis on the live
    /// trail BEFORE backtracking, mirroring drat-trim's `analyze()`.
    ///
    /// Also identifies clause literals that were ASSUMED but never reached
    /// during conflict analysis — these are candidates for clause reduction
    /// (drat-trim.c:174-179).
    pub(super) fn check_rup_with_deps(&mut self, clause: &[Literal]) -> RupDepsResult {
        self.stats.checks += 1;
        self.bcp_conflict_cidx = None;
        if self.inconsistent {
            return RupDepsResult {
                is_rup: true,
                deps: Vec::new(),
                reducible_positions: Vec::new(),
            };
        }
        let saved = self.trail.len();
        if clause.iter().any(|&lit| self.value(lit) == Some(true)) {
            return RupDepsResult {
                is_rup: true,
                deps: Vec::new(),
                reducible_positions: Vec::new(),
            };
        }
        // Track which clause positions were actually assumed (assigned).
        // Literals that are already true on the trail are NOT assumed.
        let mut assumed_positions: Vec<usize> = Vec::new();
        for (pos, &lit) in clause.iter().enumerate() {
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {}
                Some(false) => {
                    self.backtrack(saved);
                    return RupDepsResult {
                        is_rup: true,
                        deps: Vec::new(),
                        reducible_positions: Vec::new(),
                    };
                }
                None => {
                    self.assign(neg); // assumption, no reason clause
                    assumed_positions.push(pos);
                }
            }
        }
        let no_conflict = self.propagate();
        let (deps, reducible_positions) = if !no_conflict {
            self.collect_conflict_deps_with_reduction(saved, clause, &assumed_positions)
        } else {
            (Vec::new(), Vec::new())
        };
        self.backtrack(saved);
        RupDepsResult {
            is_rup: !no_conflict,
            deps,
            reducible_positions,
        }
    }

    /// Walk the trail backward (MARK-based) to collect exactly the clause
    /// indices in the resolution proof chain. Mirrors drat-trim's `analyze()`
    /// (drat-trim.c:164-184). Must be called BEFORE backtracking.
    ///
    /// Starts from the conflict clause (stored in `bcp_conflict_cidx`),
    /// marks its variables, then walks the trail backward. For each marked
    /// variable with a reason clause, adds the reason to deps and marks
    /// that reason clause's variables. This precisely collects only the
    /// clauses in the RUP derivation chain.
    ///
    /// Also identifies reducible literals: clause positions that were ASSUMED
    /// but never reached via MARK during the conflict walk. The check runs
    /// BEFORE clearing marks (drat-trim.c:174-179).
    ///
    /// Uses persistent `conflict_marked` array + dirty list to avoid
    /// allocating `vec![false; num_vars]` on every call. Only touched
    /// indices are cleared.
    fn collect_conflict_deps_with_reduction(
        &mut self,
        saved: usize,
        clause: &[Literal],
        assumed_positions: &[usize],
    ) -> (Vec<usize>, Vec<usize>) {
        let mut deps = Vec::new();

        // Start from the conflict clause: mark all its variables.
        if let Some(conflict_cidx) = self.bcp_conflict_cidx {
            deps.push(conflict_cidx);
            if let Some(conflict_clause) = self.clauses.get(conflict_cidx).and_then(|c| c.as_ref())
            {
                for &lit in conflict_clause.iter() {
                    let vi = lit.variable().index();
                    if vi < self.conflict_marked.len() && !self.conflict_marked[vi] {
                        self.conflict_marked[vi] = true;
                        self.conflict_marked_dirty.push(vi);
                    }
                }
            }
        }

        // Walk trail backward from the top. For each marked variable with a
        // reason clause, add the reason to deps and mark all its literals.
        for i in (saved..self.trail.len()).rev() {
            let lit = self.trail[i];
            let vi = lit.variable().index();
            if vi >= self.conflict_marked.len() || !self.conflict_marked[vi] {
                continue;
            }
            if let Some(reason_cidx) = self.reasons[vi] {
                if reason_cidx < self.clauses.len() {
                    deps.push(reason_cidx);
                    if let Some(ref reason_clause) = self.clauses[reason_cidx] {
                        for &rlit in reason_clause.iter() {
                            let rvi = rlit.variable().index();
                            if rvi < self.conflict_marked.len() && !self.conflict_marked[rvi] {
                                self.conflict_marked[rvi] = true;
                                self.conflict_marked_dirty.push(rvi);
                            }
                        }
                    }
                }
            }
        }

        // Identify reducible positions BEFORE clearing marks.
        // An assumed literal whose variable was NOT marked during the conflict
        // derivation is unused — it can be removed from the clause.
        // drat-trim.c:174-179.
        let reducible = assumed_positions
            .iter()
            .copied()
            .filter(|&pos| {
                let vi = clause[pos].variable().index();
                vi >= self.conflict_marked.len() || !self.conflict_marked[vi]
            })
            .collect();

        // Clean up: reset only the indices we touched.
        for i in 0..self.conflict_marked_dirty.len() {
            let vi = self.conflict_marked_dirty[i];
            self.conflict_marked[vi] = false;
        }
        self.conflict_marked_dirty.clear();

        (deps, reducible)
    }
}
