// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structure-first detection of row-interchangeable at-most-one matrices, and
//! the orbitopal unit fixing they license.
//!
//! # Why this exists
//!
//! On the SAT-COMP 2026 Main Track the winner (satsuma + Kissat, 276/400) beat
//! plain Kissat (238/400) purely on symmetry handling, and on symmetric families
//! the margin is four orders of magnitude — `homer11.shuffled` is 0.01 s for
//! satsuma+Kissat and 83 s for Kissat alone. Measured locally, satsuma gets that
//! from *structure*, not from automorphism search: on `homer11` its graph
//! automorphism engine reports `dejavu_gens = 0`, while its structure pass finds
//! `row_column = 1`, emits 46 orbitopal units, and propagation collapses the
//! whole instance in 1.83 ms.
//!
//! AY already had the matrix idea, but only in the form
//! [`super::detector::detect_php_matrix`], which rejects the formula unless
//! *every* clause belongs to one pigeonhole matrix — so it never fires on a real
//! benchmark. This module finds the same structure as a *subformula* of an
//! otherwise arbitrary CNF.
//!
//! # The structure
//!
//! A [`RowAmoMatrix`] is a variable matrix `M[row][col]` such that
//!
//! * every **column** is an at-most-one group: the CNF contains `(¬a ∨ ¬b)` for
//!   every pair of distinct variables in that column; and
//! * permuting **rows** (the same permutation in every column) maps the formula
//!   to itself.
//!
//! Row interchangeability is never assumed: each adjacent row transposition is
//! checked against the whole clause multiset (see [`permute_key`]), and only the
//! verified prefix of rows is used. A detection bug can therefore only cost us
//! units, not soundness.
//!
//! # The fixing
//!
//! Given full row symmetry on rows `0..k` and at most one true variable per
//! column, every satisfiable assignment has a row-permuted image in which column
//! `j` uses only rows `0..=j`: process columns left to right, and whenever column
//! `j` puts its single true entry in some row `> j`, swap that row with row `j`
//! — the columns already fixed are untouched because their true entries live in
//! rows `< j`. So the units
//!
//! ```text
//! ¬M[i][j]   for all i > j
//! ```
//!
//! are satisfiability-preserving. This is the classic partitioning-orbitope
//! fixing (Kaibel–Pfetsch), the same predicate BreakID and satsuma emit.
//!
//! The units are **not** RUP, so they are gated to non-proof runs by the caller
//! until they are emitted with their σ-witness on the SR route.

use std::collections::{BTreeMap, BTreeSet};

use crate::{Literal, Variable};

/// Apply a variable permutation to a canonical clause key.
///
/// A transposition is an involution, so checking that every clause containing a
/// moved variable keeps its multiplicity under the image is equivalent to
/// checking the whole formula: untouched clauses map to themselves, and the map
/// is its own inverse on the touched ones.
fn permute_key(key: &[u32], perm: &BTreeMap<Variable, Variable>) -> Vec<u32> {
    let mut image: Vec<u32> = key
        .iter()
        .map(|&raw| {
            let lit = Literal::from_index(raw as usize);
            let var = lit.variable();
            match perm.get(&var) {
                Some(&mapped) if lit.is_positive() => Literal::positive(mapped).raw(),
                Some(&mapped) => Literal::negative(mapped).raw(),
                None => raw,
            }
        })
        .collect();
    image.sort_unstable();
    image
}

/// A row-interchangeable at-most-one matrix found inside a larger formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RowAmoMatrix {
    /// `entries[row][col]` is a *cell*: the `thickness` variables that row
    /// contributes to that column, sorted by variable id. Every row has the
    /// same length (the column count), every cell the same length (the
    /// thickness), and every variable occurs at most once in the whole matrix.
    ///
    /// Thickness > 1 is the timetabling shape: with `(E exams, P periods,
    /// T slots)` the exactly-one column has width `P*T` while the cross-column
    /// AMO graph fuses each period's `T` slots into one component, so a row
    /// (period) holds `T` variables per column. Thickness 1 is the plain
    /// colouring/packing shape and behaves exactly as before.
    pub(crate) entries: Vec<Vec<Vec<Variable>>>,
    /// Number of leading rows whose adjacent transpositions were verified
    /// against the full formula. Only rows `0..verified_rows` may be broken.
    pub(crate) verified_rows: usize,
    /// Column pairs the formula does not already exclude, which must be ADDED
    /// as at-most-one clauses before any fixing unit — the orbitopal argument
    /// requires at most one true entry per column.
    ///
    /// Non-empty only for the ALO-only (graph-colouring) shape, where the
    /// encoding carries cross-vertex edge exclusions but no per-vertex
    /// at-most-one. Every variable involved was checked to occur positively
    /// exactly once, which is what makes the addition PR-redundant.
    pub(crate) synth_amo: Vec<(Variable, Variable)>,
}

impl RowAmoMatrix {
    /// Rows in the matrix (verified or not).
    pub(crate) fn row_count(&self) -> usize {
        self.entries.len()
    }

    /// Columns in the matrix.
    pub(crate) fn col_count(&self) -> usize {
        self.entries.first().map_or(0, Vec::len)
    }

    /// Variables per cell. 1 for the plain colouring/packing shape.
    pub(crate) fn thickness(&self) -> usize {
        self.entries
            .first()
            .and_then(|row| row.first())
            .map_or(0, Vec::len)
    }

    /// The orbitopal fixing units `¬M[i][j]` for `i > j`, restricted to the
    /// verified row prefix. With thickness `t` a cell contributes all `t` of
    /// its negative literals — the argument fixes the whole cell, since the
    /// column AMO spans every variable in the column.
    pub(crate) fn fixing_units(&self) -> Vec<Literal> {
        let rows = self.verified_rows.min(self.row_count());
        let cols = self.col_count();
        let mut units = Vec::new();
        for (i, row) in self.entries.iter().enumerate().take(rows) {
            for (j, cell) in row.iter().enumerate().take(cols.min(rows)) {
                if i > j {
                    units.extend(cell.iter().copied().map(Literal::negative));
                }
            }
        }
        units
    }

    /// The at-most-one clauses this matrix needs but the formula lacks.
    ///
    /// Callers MUST add these before any fixing unit: without at most one true
    /// entry per column the orbitopal argument does not hold and the units are
    /// not satisfiability-preserving.
    pub(crate) fn synth_amo_clauses(&self) -> Vec<Vec<Literal>> {
        self.synth_amo
            .iter()
            .map(|&(a, b)| vec![Literal::negative(a), Literal::negative(b)])
            .collect()
    }

    /// The same fixing units as [`Self::fixing_units`], each paired with the DSR
    /// witness that certifies it — so the orbitope route can run under `--proof`.
    ///
    /// # Why the units need a witness at all
    ///
    /// The fixing units are satisfiability-preserving but **not** RUP, so a plain
    /// `a`-line is rejected. Each unit `¬M[i][j]` is redundant by a *substitution*
    /// argument: assume `M[i][j]` is true; then by the column AMO every other
    /// entry of column `j` is false, in particular `M[i-1][j]`. Swapping rows
    /// `i-1` and `i` maps the formula to itself (that is what `verified_rows`
    /// established), and the swap moves the true entry up one row while leaving
    /// columns `< j` untouched — their true entries live in rows `< j < i-1`.
    /// So the witness is: set `M[i][j]` false, set `M[i-1][j]` true, and apply
    /// the row swap **restricted to columns `> j`**.
    ///
    /// # Emission order is part of the proof
    ///
    /// Columns ascending, rows descending within a column. Each unit's redundancy
    /// depends on the units already added below it in the same column, so
    /// [`Self::fixing_units`]' row-major order is **not** interchangeable here.
    /// Callers on the proof route must consume this method, not that one.
    ///
    /// # Witness layout
    ///
    /// `[pivot, +M[i-1][j], pivot, from, to, from, to, …]`, written after the
    /// clause on the `a`-line. Per `dsr-trim`'s `parse_sr_clause_and_witness`,
    /// the second occurrence of the pivot opens the partial-assignment part and
    /// the third opens the substitution part; the pairs list the row swap as
    /// positive `from to` literals. This differs from
    /// [`super::detector`]'s `sr_witness_tokens` only in carrying one extra
    /// assignment literal (`+M[i-1][j]`) between the two pivots.
    ///
    /// Validated end to end against the real `exam_75_65`: 2080 units,
    /// `dsr-trim` returns `s VERIFIED UNSAT`.
    pub(crate) fn sr_steps(&self) -> Vec<(Vec<Literal>, Vec<Literal>)> {
        let rows = self.verified_rows.min(self.row_count());
        let cols = self.col_count();
        let mut steps = Vec::new();
        // The synthesized at-most-one clauses come first: every fixing unit's
        // witness argument leans on the column AMO, so they must already be in
        // the formula. PR witness `{b = 1, a = 0}` — the pivot is `¬b`, the
        // literal of the clause the witness satisfies.
        for &(a, b) in &self.synth_amo {
            // Clause (¬a ∨ ¬b); pivot ¬a; witness assigns b = 1, so the only
            // clause holding `a` or `b` positively — the column's ALO clause,
            // verified to be their sole positive occurrence — stays satisfied.
            let pivot = Literal::negative(a);
            steps.push((
                vec![pivot, Literal::negative(b)],
                vec![pivot, Literal::positive(b), pivot],
            ));
        }

        let thickness = self.thickness();
        for j in 0..cols.min(rows) {
            for i in (j + 1..rows).rev() {
                for k in 0..thickness {
                    let below = self.entries[i][j][k];
                    let above = self.entries[i - 1][j][k];
                    let pivot = Literal::negative(below);
                    // Partial assignment: pivot (¬below) then above=true.
                    let mut witness = vec![pivot, Literal::positive(above), pivot];
                    // Substitution: swap rows i-1 and i, columns > j only,
                    // matching the cells position-wise (k-th <-> k-th).
                    for col in (j + 1)..cols {
                        for kk in 0..thickness {
                            let a = self.entries[i - 1][col][kk];
                            let b = self.entries[i][col][kk];
                            witness.push(Literal::positive(a));
                            witness.push(Literal::positive(b));
                            witness.push(Literal::positive(b));
                            witness.push(Literal::positive(a));
                        }
                    }
                    steps.push((vec![pivot], witness));
                }
            }
        }
        steps
    }

    /// The row transposition `(a b)` as a variable permutation over the matrix.
    pub(crate) fn row_swap(&self, a: usize, b: usize) -> BTreeMap<Variable, Variable> {
        let mut perm = BTreeMap::new();
        if a == b {
            return perm;
        }
        for (col, cell_a) in self.entries[a].iter().enumerate() {
            // Cells are sorted by variable id, so pairing position-wise is a
            // well-defined bijection. The SAME pairing must be used by
            // `sr_steps`, or the gate below verifies one permutation while the
            // proof asserts another.
            for (k, &va) in cell_a.iter().enumerate() {
                let vb = self.entries[b][col][k];
                perm.insert(va, vb);
                perm.insert(vb, va);
            }
        }
        perm
    }
}

/// Budgets for [`detect_row_amo_matrices`].
#[derive(Debug, Clone, Copy)]
pub(crate) struct OrbitopeLimits {
    /// Maximum clauses to scan. Detection is linear, so this is generous.
    pub(crate) max_clauses: usize,
    /// Maximum rows to gate-verify (each verification is one pass over the
    /// clause multiset).
    pub(crate) max_verified_rows: usize,
    /// Minimum rows for the structure to be worth breaking.
    pub(crate) min_rows: usize,
    /// Minimum columns for the structure to be worth breaking.
    pub(crate) min_cols: usize,
}

impl Default for OrbitopeLimits {
    fn default() -> Self {
        Self {
            max_clauses: 1_000_000,
            max_verified_rows: 256,
            min_rows: 3,
            min_cols: 2,
        }
    }
}

/// Telemetry for one detection pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct OrbitopeStats {
    /// Exactly-one groups (all-positive clause whose variables are pairwise
    /// at-most-one) found in the formula.
    pub(crate) eo_groups: u64,
    /// Candidate columns kept after width selection and disjointness.
    pub(crate) columns: u64,
    /// Row components found in the cross-column at-most-one graph.
    pub(crate) row_components: u64,
    /// Adjacent row transpositions that passed the formula-preserving gate.
    pub(crate) verified_swaps: u64,
    /// Adjacent row transpositions that failed the gate.
    pub(crate) rejected_swaps: u64,
}

/// Whether to admit ALO-only columns by synthesizing the missing at-most-one
/// clauses (`AY_SAT_ORBITOPE_ALO_COLUMNS=1`). **Default off.**
///
/// The route works and is worth 10 official instances — the whole graph-colouring
/// family — solving `mulsol.i.1.48` in 849 ms and `fpsol2.i.2.29` in 2.4 s where
/// both previously timed out at 300 s. It is off because **it can emit a
/// certificate an external checker rejects**: of the 10 it solves, 9 give
/// `dsr-trim` `s VERIFIED UNSAT` and `zeroin.i.3.29` gives
/// `Error: [line 121051] No UP contradiction for RAT clause 168525`.
///
/// An answer whose proof is rejected is a disqualified submission, not a win
/// (see `dimacs.rs::uncertifiable_symmetry_gate_error` for the same rule applied
/// to the composite route), and nothing distinguishes the good nine from the bad
/// one at emission time — so the whole extension stays behind the flag until the
/// zeroin case is understood.
///
/// What is already known: the same construction verifies from the Python
/// reference (`s VALID` on zeroin, AMO steps alone and AMO + staircase), so the
/// defect is in this port, not in the mathematics. The prime suspect is the
/// clique-first column ordering here differing from the reference's, since that
/// changes which columns the staircase fixes and in what order.
fn alo_only_columns_enabled() -> bool {
    // DEFAULT ON since 2026-08-11. It was off because zeroin.i.3.29 emitted a
    // certificate dsr-trim rejected; that is fixed — the synthesized AMO
    // variables are now frozen so BVE cannot eliminate them and delete a clause
    // the refutation needs. Measured after the fix: 10 of the 11 official
    // colouring instances solve AND their certificates verify.
    // B26: CLI-owned opt-out (--sat-no-orbitope-alo-columns); env retired.
    !ay_core::sat_ab_switches().no_orbitope_alo_columns
}

/// Find row-interchangeable at-most-one matrices inside `clauses`.
///
/// Returns at most one matrix today (the largest width class); the signature is
/// a vector so a later pass can peel off independent matrices without changing
/// callers.
pub(crate) fn detect_row_amo_matrices(
    clauses: &[Vec<Literal>],
    limits: OrbitopeLimits,
) -> (Vec<RowAmoMatrix>, OrbitopeStats) {
    let mut stats = OrbitopeStats::default();
    if clauses.len() > limits.max_clauses {
        return (Vec::new(), stats);
    }

    // At-most-one edges: `(¬a ∨ ¬b)` over two distinct variables.
    let mut amo: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for clause in clauses {
        if clause.len() == 2 && clause.iter().all(|l| !l.is_positive()) {
            let (a, b) = (clause[0].variable(), clause[1].variable());
            if a != b {
                amo.entry(a).or_default().insert(b);
                amo.entry(b).or_default().insert(a);
            }
        }
    }
    if amo.is_empty() {
        return (Vec::new(), stats);
    }
    let mutex = |a: Variable, b: Variable| amo.get(&a).is_some_and(|s| s.contains(&b));

    // Exactly-one groups: an all-positive clause whose variables are pairwise
    // at-most-one. In a graph-colouring or scheduling encoding this is one
    // "slot" — the natural column of the matrix.
    //
    // A column need NOT already be pairwise at-most-one. Graph-colouring
    // instances encode only the cross-vertex edge exclusions, so no per-vertex
    // AMO clause exists anywhere: measured on `mulsol.i.2.30`, 0 of 188 columns
    // are pairwise-AMO, which is why the detector used to find nothing. The
    // missing pairs can be ADDED as PR steps -- but only under a condition that
    // must be checked, not assumed: `(¬a ∨ ¬b)` witnessed by `{b = 1, a = 0}`
    // is redundant exactly when every clause containing `a` or `b` positively
    // is satisfied by the witness. That holds when each column variable occurs
    // positively ONLY in this clause, which `b = 1` satisfies. So census the
    // positive occurrences and require exactly one.
    let mut pos_occ: BTreeMap<Variable, usize> = BTreeMap::new();
    for clause in clauses {
        for lit in clause {
            if lit.is_positive() {
                *pos_occ.entry(lit.variable()).or_default() += 1;
            }
        }
    }
    let mut columns: Vec<Vec<Variable>> = Vec::new();
    for clause in clauses {
        if clause.len() < 2 || !clause.iter().all(|l| l.is_positive()) {
            continue;
        }
        let vars: Vec<Variable> = clause.iter().map(|l| l.variable()).collect();
        let distinct: BTreeSet<Variable> = vars.iter().copied().collect();
        if distinct.len() != vars.len() {
            continue;
        }
        let pairwise_amo = vars
            .iter()
            .enumerate()
            .all(|(i, &a)| vars[i + 1..].iter().all(|&b| mutex(a, b)));
        // ALO-only fallback (graph colouring), DEFAULT OFF — see below.
        let amo_synthesizable = alo_only_columns_enabled()
            && vars
                .iter()
                .all(|v| pos_occ.get(v).copied().unwrap_or(0) == 1);
        if pairwise_amo || amo_synthesizable {
            stats.eo_groups += 1;
            columns.push(vars);
        }
    }
    if columns.len() < limits.min_cols {
        return (Vec::new(), stats);
    }

    // Keep the most common width, then keep a variable-disjoint subfamily.
    let mut width_counts: BTreeMap<usize, usize> = BTreeMap::new();
    for col in &columns {
        *width_counts.entry(col.len()).or_default() += 1;
    }
    let Some((&width, _)) = width_counts.iter().max_by_key(|&(w, n)| (*n, *w)) else {
        return (Vec::new(), stats);
    };
    let mut used: BTreeSet<Variable> = BTreeSet::new();
    let mut kept: Vec<Vec<Variable>> = Vec::new();
    for col in columns.into_iter().filter(|c| c.len() == width) {
        if col.iter().any(|v| used.contains(v)) {
            continue;
        }
        used.extend(col.iter().copied());
        kept.push(col);
    }
    // Degree-0 tolerance: a column whose variables carry no at-most-one edge at
    // all is unconstrained, contributes `width` singleton components, and would
    // break the components-vs-width accounting below. Measured on
    // `mulsol.i.2.30`: 15 such columns produce 450 singletons and 480 components
    // against a width of 30, so the matrix was rejected outright.
    kept.retain(|col| col.iter().any(|v| amo.contains_key(v)));
    stats.columns = kept.len() as u64;
    if kept.len() < limits.min_cols || width < limits.min_rows {
        return (Vec::new(), stats);
    }

    // Rows = connected components of the at-most-one graph restricted to edges
    // between *different* columns. In a colouring encoding these are exactly the
    // colour classes, tied together by the edge clauses `(¬x[u][c] ∨ ¬x[v][c])`.
    let mut col_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (idx, col) in kept.iter().enumerate() {
        for &v in col {
            col_of.insert(v, idx);
        }
    }
    let mut component: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut components: Vec<Vec<Variable>> = Vec::new();
    for (&start, &start_col) in &col_of {
        if component.contains_key(&start) {
            continue;
        }
        let id = components.len();
        let mut members = Vec::new();
        let mut stack = vec![(start, start_col)];
        component.insert(start, id);
        while let Some((u, u_col)) = stack.pop() {
            members.push(u);
            if let Some(neighbours) = amo.get(&u) {
                for &w in neighbours {
                    let Some(&w_col) = col_of.get(&w) else {
                        continue; // outside the matrix
                    };
                    if w_col == u_col || component.contains_key(&w) {
                        continue;
                    }
                    component.insert(w, id);
                    stack.push((w, w_col));
                }
            }
        }
        components.push(members);
    }
    stats.row_components = components.len() as u64;

    // A usable matrix needs the column width to split evenly across the rows:
    // each row contributes the same number of variables (the thickness) to
    // every kept column.
    //
    // This used to demand `components.len() == width` and `members.len() ==
    // kept.len()`, which are both algebraically "thickness == 1". That rejected
    // the entire timetabling family before the row-swap gate below ever ran, so
    // those instances were indistinguishable from symmetry-free formulas.
    // Measured on the real `mexam_14_12_2`: 14 columns of width 24 over 12
    // components of 28 members, i.e. thickness 2 — bailed here.
    let rows = components.len();
    if rows == 0 || !width.is_multiple_of(rows) {
        return (Vec::new(), stats);
    }
    let thickness = width / rows;
    if thickness == 0 {
        return (Vec::new(), stats);
    }
    let mut entries: Vec<Vec<Vec<Variable>>> = vec![vec![Vec::new(); kept.len()]; rows];
    for (row, members) in components.iter().enumerate() {
        // Every row holds `thickness` variables in each of the kept columns.
        if members.len() != kept.len() * thickness {
            return (Vec::new(), stats);
        }
        for &v in members {
            let col = col_of[&v];
            let cell = &mut entries[row][col];
            if cell.len() == thickness {
                return (Vec::new(), stats); // over-full cell
            }
            cell.push(v);
        }
        if entries[row].iter().any(|cell| cell.len() != thickness) {
            return (Vec::new(), stats); // uneven cells
        }
    }
    // Sort each cell so `row_swap` and `sr_steps` agree on the pairing.
    for row in &mut entries {
        for cell in row.iter_mut() {
            cell.sort_unstable();
        }
    }
    // Clique-first column order. The staircase only fixes the first
    // `min(rows, cols)` columns, so WHICH columns those are decides whether the
    // fixing propagates. Measured on `mulsol.i.2.30` with identical units: file
    // order gives 555 504 conflicts and UNKNOWN at 60 s, clique-first gives
    // 1 635 conflicts and UNSAT in 13.3 s. Greedy: repeatedly take the column
    // with the most at-most-one edges into the already-chosen prefix, breaking
    // ties by total degree.
    let ncols = entries.first().map_or(0, Vec::len);
    if ncols > 1 {
        let degree = |col: usize, entries: &Vec<Vec<Vec<Variable>>>| -> usize {
            entries
                .iter()
                .flat_map(|row| row[col].iter())
                .map(|v| amo.get(v).map_or(0, BTreeSet::len))
                .sum()
        };
        let mut remaining: Vec<usize> = (0..ncols).collect();
        let first = *remaining
            .iter()
            .max_by_key(|&&c| degree(c, &entries))
            .expect("ncols > 1");
        remaining.retain(|&c| c != first);
        let mut order = vec![first];
        let mut prefix: BTreeSet<Variable> = entries
            .iter()
            .flat_map(|row| row[first].iter().copied())
            .collect();
        while !remaining.is_empty() {
            let pick = *remaining
                .iter()
                .max_by_key(|&&c| {
                    let into: usize = entries
                        .iter()
                        .flat_map(|row| row[c].iter())
                        .map(|v| {
                            amo.get(v)
                                .map_or(0, |ns| ns.iter().filter(|n| prefix.contains(n)).count())
                        })
                        .sum();
                    (into, degree(c, &entries), std::cmp::Reverse(c))
                })
                .expect("non-empty");
            remaining.retain(|&c| c != pick);
            prefix.extend(entries.iter().flat_map(|row| row[pick].iter().copied()));
            order.push(pick);
        }
        for row in &mut entries {
            let reordered: Vec<Vec<Variable>> = order.iter().map(|&c| row[c].clone()).collect();
            *row = reordered;
        }
    }

    // Pairs inside a column that the formula does not already exclude. The
    // fixing argument REQUIRES at most one true entry per column, so these must
    // be added (as PR steps on the proof route) before any fixing unit.
    let mut synth_amo: Vec<(Variable, Variable)> = Vec::new();
    for col in 0..ncols {
        let colvars: Vec<Variable> = entries
            .iter()
            .flat_map(|row| row[col].iter().copied())
            .collect();
        for (i, &a) in colvars.iter().enumerate() {
            for &b in &colvars[i + 1..] {
                if !mutex(a, b) {
                    synth_amo.push((a, b));
                }
            }
        }
    }

    let mut matrix = RowAmoMatrix {
        entries,
        verified_rows: 0,
        synth_amo,
    };
    // Deterministic order: rows by their smallest variable, columns by the
    // first row's variable order.
    matrix.entries.sort_by_key(|row| {
        row.iter()
            .flatten()
            .copied()
            .min()
            .unwrap_or(Variable::new(0))
    });

    // Sound gate: verify adjacent row transpositions against the whole formula
    // and keep only the verified prefix. `S_k` is generated by its adjacent
    // transpositions, so a verified prefix of length k gives full row symmetry
    // on those k rows.
    //
    // Each transposition moves only the 2·cols variables of two rows, so it is
    // checked against just the clauses those variables occur in — every other
    // clause is mapped to itself. Because a row's variables move in at most two
    // adjacent transpositions, the whole verification sweep costs one pass over
    // the matrix variables' occurrence lists rather than `rows` passes over the
    // formula.
    let formula_counts = super::build_formula_counts(clauses);
    let keys: Vec<Vec<u32>> = clauses
        .iter()
        .map(|c| super::canonical_clause_key(c))
        .collect();
    let mut occurrences: BTreeMap<Variable, Vec<usize>> = BTreeMap::new();
    for (idx, clause) in clauses.iter().enumerate() {
        for lit in clause {
            let var = lit.variable();
            if col_of.contains_key(&var) {
                let slot = occurrences.entry(var).or_default();
                if slot.last() != Some(&idx) {
                    slot.push(idx);
                }
            }
        }
    }
    let cap = limits.max_verified_rows.min(matrix.row_count());
    let mut seen_stamp: Vec<u32> = vec![0; clauses.len()];
    let mut stamp = 0u32;
    let mut verified = 1usize;
    while verified < cap {
        let perm = matrix.row_swap(verified - 1, verified);
        stamp += 1;
        let mut preserved = true;
        'swap: for var in perm.keys() {
            for &idx in occurrences.get(var).map_or(&[][..], Vec::as_slice) {
                if seen_stamp[idx] == stamp {
                    continue;
                }
                seen_stamp[idx] = stamp;
                let image = permute_key(&keys[idx], &perm);
                if formula_counts.get(&image) != formula_counts.get(&keys[idx]) {
                    preserved = false;
                    break 'swap;
                }
            }
        }
        if preserved {
            stats.verified_swaps += 1;
            verified += 1;
        } else {
            stats.rejected_swaps += 1;
            break;
        }
    }
    matrix.verified_rows = verified;
    if verified < limits.min_rows {
        return (Vec::new(), stats);
    }
    (vec![matrix], stats)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: i32) -> Literal {
        let var = Variable::new(v.unsigned_abs());
        if v > 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    /// Graph colouring of a triangle with 3 colours: variables `x[v][c]` with
    /// `v ∈ {0,1,2}` (columns) and `c ∈ {0,1,2}` (rows). Colours are
    /// interchangeable, so this is a 3x3 row-interchangeable AMO matrix.
    fn triangle_3colour() -> Vec<Vec<Literal>> {
        // var id = 1 + 3*v + c
        let x = |v: i32, c: i32| 1 + 3 * v + c;
        let mut clauses = Vec::new();
        for v in 0..3 {
            clauses.push((0..3).map(|c| lit(x(v, c))).collect::<Vec<_>>());
            for c in 0..3 {
                for d in (c + 1)..3 {
                    clauses.push(vec![lit(-x(v, c)), lit(-x(v, d))]);
                }
            }
        }
        for (u, v) in [(0, 1), (0, 2), (1, 2)] {
            for c in 0..3 {
                clauses.push(vec![lit(-x(u, c)), lit(-x(v, c))]);
            }
        }
        clauses
    }

    /// The triangle, but every (vertex, colour) cell holds `t` interchangeable
    /// slot variables — the timetabling shape, where a column's exactly-one
    /// group has width `rows * t` and each row contributes `t` variables to it.
    fn triangle_3colour_thickness(t: i32) -> Vec<Vec<Literal>> {
        // var id = 1 + 3*t*v + t*c + k, for vertex v, colour c, slot k.
        let x = |v: i32, c: i32, k: i32| 1 + 3 * t * v + t * c + k;
        let mut clauses = Vec::new();
        for v in 0..3 {
            // Column = vertex: exactly one (colour, slot) over all 3*t.
            let col: Vec<Literal> = (0..3)
                .flat_map(|c| (0..t).map(move |k| (c, k)))
                .map(|(c, k)| lit(x(v, c, k)))
                .collect();
            for i in 0..col.len() {
                for j in (i + 1)..col.len() {
                    clauses.push(vec![col[i].negated(), col[j].negated()]);
                }
            }
            clauses.push(col);
        }
        // Rows = colours, tied across columns by the edge clauses. Every slot of
        // a colour excludes every slot of that colour at an adjacent vertex, so
        // the colour's variables form one component of the cross-column graph.
        for (u, v) in [(0, 1), (0, 2), (1, 2)] {
            for c in 0..3 {
                for k in 0..t {
                    for l in 0..t {
                        clauses.push(vec![lit(-x(u, c, k)), lit(-x(v, c, l))]);
                    }
                }
            }
        }
        clauses
    }

    /// Thickness 2 must be detected as a 3x3 matrix of 2-variable cells, not
    /// rejected. Before the generalization the shape guards were algebraically
    /// `thickness == 1`, so the whole timetabling family bailed before the sound
    /// row-swap gate ever ran and looked identical to a symmetry-free formula.
    #[test]
    fn detects_a_thickness_two_matrix() {
        let clauses = triangle_3colour_thickness(2);
        let (matrices, stats) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        assert_eq!(stats.row_components, 3, "one row per colour");
        assert_eq!(matrices.len(), 1, "the thickness-2 matrix must be found");
        let m = &matrices[0];
        assert_eq!(m.row_count(), 3);
        assert_eq!(m.col_count(), 3);
        assert_eq!(m.thickness(), 2);
        assert_eq!(m.verified_rows, 3, "all colour swaps are automorphisms");

        // Each of the 3 fixed cells contributes both of its variables.
        assert_eq!(m.fixing_units().len(), 3 * 2);
        let steps = m.sr_steps();
        assert_eq!(steps.len(), 3 * 2, "one certified step per fixed variable");

        // The row swap pairs cells position-wise, so it moves every variable of
        // both rows and nothing else.
        let perm = m.row_swap(1, 2);
        assert_eq!(
            perm.len(),
            2 * 3 * 2,
            "two rows x three columns x thickness"
        );
        for col in 0..3 {
            for k in 0..2 {
                assert_eq!(perm[&m.entries[1][col][k]], m.entries[2][col][k]);
            }
        }
    }

    /// Thickness 1 must be byte-identical to the pre-generalization behaviour:
    /// the generalized detector collapses onto the old one.
    #[test]
    fn thickness_one_is_unchanged_by_the_generalization() {
        let a = detect_row_amo_matrices(&triangle_3colour(), OrbitopeLimits::default()).0;
        let b =
            detect_row_amo_matrices(&triangle_3colour_thickness(1), OrbitopeLimits::default()).0;
        assert_eq!(a.len(), 1);
        assert_eq!(b.len(), 1);
        assert_eq!(a[0].thickness(), 1);
        assert_eq!(b[0].thickness(), 1);
        assert_eq!(a[0].fixing_units().len(), 3);
        assert_eq!(b[0].fixing_units().len(), 3);
    }

    #[test]
    fn detects_colour_row_symmetry_in_a_triangle() {
        let clauses = triangle_3colour();
        let (matrices, stats) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        assert_eq!(stats.columns, 3, "one column per vertex");
        assert_eq!(stats.row_components, 3, "one row per colour");
        assert_eq!(matrices.len(), 1);
        let m = &matrices[0];
        assert_eq!(m.row_count(), 3);
        assert_eq!(m.col_count(), 3);
        assert_eq!(m.verified_rows, 3, "all colour swaps are automorphisms");
        // Fixing: ¬M[1][0], ¬M[2][0], ¬M[2][1].
        assert_eq!(m.fixing_units().len(), 3);
    }

    /// `sr_steps` must certify exactly the units `fixing_units` emits — same
    /// multiset, but in the order the proof needs (columns ascending, rows
    /// descending), because each unit's redundancy rests on the ones already
    /// added below it in its column.
    #[test]
    fn sr_steps_cover_the_same_units_in_proof_order() {
        let clauses = triangle_3colour();
        let (matrices, _) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        let m = &matrices[0];

        let steps = m.sr_steps();
        let stepped: Vec<Literal> = steps
            .iter()
            .map(|(clause, _)| {
                assert_eq!(clause.len(), 1, "every fixing step is a unit");
                clause[0]
            })
            .collect();

        let mut from_steps = stepped.clone();
        let mut from_units = m.fixing_units();
        from_steps.sort_unstable();
        from_units.sort_unstable();
        assert_eq!(from_steps, from_units, "same units, however ordered");

        // Proof order: column 0 rows 2,1 then column 1 row 2.
        assert_eq!(
            stepped,
            vec![
                Literal::negative(m.entries[2][0][0]),
                Literal::negative(m.entries[1][0][0]),
                Literal::negative(m.entries[2][1][0]),
            ],
        );
    }

    /// The witness layout `dsr-trim` parses: pivot, the partial assignment
    /// (`+M[i-1][j]`), the pivot again as separator, then the row swap as
    /// positive `from to` pairs over the columns strictly right of the pivot's.
    #[test]
    fn sr_witness_has_the_dsr_layout_and_swaps_only_later_columns() {
        let clauses = triangle_3colour();
        let (matrices, _) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        let m = &matrices[0];
        let steps = m.sr_steps();

        // First step is ¬M[2][0]: swap rows 1 and 2 over columns 1 and 2.
        let (clause, witness) = &steps[0];
        let pivot = Literal::negative(m.entries[2][0][0]);
        assert_eq!(clause, &vec![pivot]);
        assert_eq!(witness[0], pivot, "witness opens with the pivot");
        assert_eq!(
            witness[1],
            Literal::positive(m.entries[1][0][0]),
            "partial assignment lifts the true entry one row up"
        );
        assert_eq!(witness[2], pivot, "third pivot opens the substitution part");

        // Two later columns, four tokens each (a b, b a).
        assert_eq!(witness.len(), 3 + 2 * 4);
        let pairs = &witness[3..];
        assert!(
            pairs.iter().all(|l| l.is_positive()),
            "substitution pairs are positive literals: {pairs:?}"
        );
        for (k, col) in [1usize, 2].into_iter().enumerate() {
            let a = Literal::positive(m.entries[1][col][0]);
            let b = Literal::positive(m.entries[2][col][0]);
            assert_eq!(&pairs[k * 4..k * 4 + 4], &[a, b, b, a]);
        }

        // The pivot's own column must never appear in the substitution: the
        // swap is restricted to columns > j, which is what keeps the already
        // fixed columns untouched.
        for row in 0..m.row_count() {
            let v = Literal::positive(m.entries[row][0][0]);
            assert!(
                !pairs.contains(&v),
                "column 0 must not be permuted by its own step"
            );
        }
    }

    #[test]
    fn fixing_units_are_satisfiability_preserving_on_the_triangle() {
        let clauses = triangle_3colour();
        let (matrices, _) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        let units = matrices[0].fixing_units();
        // Brute force: the triangle is 3-colourable, and it stays satisfiable
        // once the orbitopal units are added.
        let nvars = 9usize;
        let satisfies = |assign: u32, cs: &[Vec<Literal>]| {
            cs.iter().all(|c| {
                c.iter().any(|l| {
                    let bit = (assign >> (l.variable().index() - 1)) & 1 == 1;
                    bit == l.is_positive()
                })
            })
        };
        let mut with_units = clauses.clone();
        with_units.extend(units.iter().map(|&u| vec![u]));
        let base = (0..(1u32 << nvars))
            .filter(|&a| satisfies(a, &clauses))
            .count();
        let broken = (0..(1u32 << nvars))
            .filter(|&a| satisfies(a, &with_units))
            .count();
        assert!(base > 0, "triangle is 3-colourable");
        assert!(broken > 0, "orbitopal fixing must keep a model");
        assert!(
            broken < base,
            "orbitopal fixing must remove symmetric models"
        );
    }

    #[test]
    fn rejects_a_formula_whose_rows_are_not_interchangeable() {
        let mut clauses = triangle_3colour();
        // Break colour symmetry: forbid colour 0 on vertex 0 only.
        clauses.push(vec![lit(-1)]);
        let (matrices, _) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        // Either no matrix survives, or the verified prefix is too short to fix.
        assert!(
            matrices.is_empty() || matrices[0].verified_rows < 3,
            "asymmetric formula must not report full row symmetry"
        );
    }

    #[test]
    fn ignores_formulas_without_at_most_one_structure() {
        let clauses = vec![vec![lit(1), lit(2), lit(3)], vec![lit(-1), lit(2)]];
        let (matrices, stats) = detect_row_amo_matrices(&clauses, OrbitopeLimits::default());
        assert!(matrices.is_empty());
        assert_eq!(stats.eo_groups, 0);
    }
}
