// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Aux-free SR refutation for the phase-flipped clique-colouring family
/// (`homer*.shuffled`, task #17). Same contract as [`detect_php_aux_free_sr`]:
/// `None` when the formula is not this exact shape; the strict recognizer is
/// part of the soundness boundary because the route also runs without a proof
/// surface, and a mis-detection may only ever produce a certificate the
/// external checker rejects, never a false VERIFIED.
///
/// The structure is a pigeonhole colouring hidden behind per-variable polarity
/// flips: a uniform-width (`C > 2`) clause set covers every variable exactly
/// once (per-vertex colour "ALO rows"; a variable's in-row literal sign is its
/// PHASE), and every binary normalizes under the phase map to an all-negative
/// cross-row edge. The binary graph's connected components are the colour
/// classes — each must be a complete clique with exactly one variable per row
/// — and rows grouped by their touched class set are the clique components.
/// The chosen group (the one containing the lowest row) must have `m` rows
/// over `C` classes with `m > C`, and each of its classes must live entirely
/// inside the group (class size exactly `m`), which is what makes a colour
/// transposition confined to the group a genuine automorphism of the FULL
/// formula. Refuting one component refutes the conjunction (chnl precedent).
///
/// The chain is the colour-diagonal WLOG fixing validated externally before
/// this port (`homer18`/`homer20`: 66 steps each, `dsr-trim` `s VERIFIED
/// UNSAT`): for `t = 0..C` and `h > t`, the SR unit "vertex `t` is not colour
/// `h`" (semantic `x[t][h] = 0`, emitted through the phase map), witnessed by
/// the PR assignment `{x[t][h]=0, x[t][t]=1}` plus the colour transposition
/// `(t h)` on every other row of the group; then the RAT unit `x[t][t]`.
/// Substitution images ride the phase map: variable `a` maps to the literal
/// `(phase_a·phase_b)·b` — dsr-trim accepts signed substitution images
/// (measured). Row `C`'s ALO then dies by root unit propagation, which closes
/// the proof (the solver emits the empty clause; it is not a returned step).
pub(crate) fn detect_phased_colouring_aux_free_sr(
    clauses: &[Vec<Literal>],
) -> Option<Vec<LexClause>> {
    let grid = detect_phased_colouring_grid(clauses)?;
    Some(build_phased_colouring_chain(&grid))
}

/// Recognise the phased colouring shape (see
/// [`detect_phased_colouring_aux_free_sr`]) and return the chosen group as an
/// `m × C` grid of PHASE literals (`grid[row][colour]` is the variable's
/// in-row literal, i.e. the semantic `x = 1` polarity).
fn detect_phased_colouring_grid(clauses: &[Vec<Literal>]) -> Option<Vec<Vec<Literal>>> {
    use std::collections::{BTreeMap, BTreeSet};

    // Partition by width; anything narrower than a binary disqualifies.
    let mut rows: Vec<&Vec<Literal>> = Vec::new();
    let mut bins: Vec<&Vec<Literal>> = Vec::new();
    for c in clauses {
        match c.len() {
            0 | 1 => return None,
            2 => bins.push(c),
            _ => rows.push(c),
        }
    }
    let width = rows.first()?.len(); // > 2 by the partition
    if rows.iter().any(|r| r.len() != width) {
        return None;
    }
    // Every variable in exactly one row; its in-row sign is its phase.
    let mut row_phase: BTreeMap<Variable, (usize, Literal)> = BTreeMap::new();
    for (i, r) in rows.iter().enumerate() {
        for &l in r.iter() {
            if row_phase.insert(l.variable(), (i, l)).is_some() {
                return None;
            }
        }
    }
    // Binaries must normalize to (¬phase, ¬phase) across two different rows.
    let mut adj: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for b in &bins {
        let (la, lb) = (b[0], b[1]);
        let &(ra, pa) = row_phase.get(&la.variable())?;
        let &(rb, pb) = row_phase.get(&lb.variable())?;
        if la != pa.negated() || lb != pb.negated() || ra == rb {
            return None;
        }
        adj.entry(la.variable()).or_default().insert(lb.variable());
        adj.entry(lb.variable()).or_default().insert(la.variable());
    }
    // Colour classes = connected components of the binary graph. Each must be
    // a complete clique (degree = size - 1 suffices: neighbours never leave a
    // component and `adj` deduplicates) with at most one variable per row.
    let mut comp_of: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut comps: Vec<Vec<Variable>> = Vec::new();
    for &start in row_phase.keys() {
        if comp_of.contains_key(&start) {
            continue;
        }
        let id = comps.len();
        let mut members: Vec<Variable> = Vec::new();
        let mut stack = vec![start];
        comp_of.insert(start, id);
        while let Some(u) = stack.pop() {
            members.push(u);
            for &w in adj.get(&u).into_iter().flatten() {
                if let std::collections::btree_map::Entry::Vacant(e) = comp_of.entry(w) {
                    e.insert(id);
                    stack.push(w);
                }
            }
        }
        comps.push(members);
    }
    for members in &comps {
        let mut seen_rows: BTreeSet<usize> = BTreeSet::new();
        for &v in members {
            if !seen_rows.insert(row_phase[&v].0)
                || adj.get(&v).map_or(0, BTreeSet::len) != members.len() - 1
            {
                return None;
            }
        }
    }
    phased_colouring_group_grid(rows.len(), width, &row_phase, &comp_of, &comps)
}

/// Split the rows into groups by touched class set, pick the group containing
/// the lowest row, and build its phase-literal grid (`m × C`, `m > C`).
fn phased_colouring_group_grid(
    nrows: usize,
    width: usize,
    row_phase: &BTreeMap<Variable, (usize, Literal)>,
    comp_of: &BTreeMap<Variable, usize>,
    comps: &[Vec<Variable>],
) -> Option<Vec<Vec<Literal>>> {
    use std::collections::{BTreeMap, BTreeSet};

    let mut row_classes: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); nrows];
    for (v, &(r, _)) in row_phase {
        row_classes[r].insert(comp_of[v]);
    }
    let cls: Vec<usize> = row_classes.first()?.iter().copied().collect();
    if cls.len() != width {
        return None;
    }
    let grp: Vec<usize> = (0..nrows).filter(|&r| row_classes[r] == row_classes[0]).collect();
    let m = grp.len();
    if m <= width {
        return None; // needs strictly more vertices than colours to be UNSAT
    }
    // Every class of the group must live ENTIRELY inside it: a class member on
    // an outside row would break the colour transposition's automorphism.
    if cls.iter().any(|&ci| comps[ci].len() != m) {
        return None;
    }
    let ridx: BTreeMap<usize, usize> = grp.iter().enumerate().map(|(i, &r)| (r, i)).collect();
    let cidx: BTreeMap<usize, usize> = cls.iter().enumerate().map(|(j, &c)| (c, j)).collect();
    let mut grid: Vec<Vec<Option<Literal>>> = vec![vec![None; width]; m];
    for (v, &(r, phase)) in row_phase {
        let Some(&ri) = ridx.get(&r) else { continue };
        let cj = *cidx.get(comp_of.get(v)?)?;
        if grid[ri][cj].replace(phase).is_some() {
            return None;
        }
    }
    grid.into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<Literal>>>())
        .collect()
}

/// Emit the colour-diagonal WLOG chain over the group grid. All literals are
/// routed through the phase map: the semantic assignment `x = 1` is the phase
/// literal itself, `x = 0` its negation, and a substitution image carries the
/// sign product of the two phases.
fn build_phased_colouring_chain(grid: &[Vec<Literal>]) -> Vec<LexClause> {
    let m = grid.len();
    let width = grid.first().map_or(0, Vec::len);
    let mut out: Vec<LexClause> = Vec::new();
    for t in 0..width {
        for h in (t + 1)..width {
            // Unit "vertex t is not colour h"; witness: {x[t][h]=0, x[t][t]=1},
            // σ = colour transposition (t h) on every other row of the group.
            let piv = grid[t][h].negated();
            let mut witness = vec![piv, grid[t][t], piv];
            for row in grid.iter().take(m).enumerate().filter(|&(w, _)| w != t) {
                let (pa, pb) = (row.1[t], row.1[h]);
                let same_phase = pa.is_positive() == pb.is_positive();
                let image = |l: Literal| {
                    if same_phase {
                        Literal::positive(l.variable())
                    } else {
                        Literal::negative(l.variable())
                    }
                };
                witness.push(Literal::positive(pa.variable()));
                witness.push(image(pb));
                witness.push(Literal::positive(pb.variable()));
                witness.push(image(pa));
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        // RAT unit "vertex t IS colour t" (pivot-only PR witness).
        out.push(LexClause::Sr {
            clause: vec![grid[t][t]],
            witness: vec![grid[t][t]],
        });
    }
    out
}
