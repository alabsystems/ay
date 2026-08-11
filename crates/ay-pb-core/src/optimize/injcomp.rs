// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact certified optimum for the NORDSTROM CoreGuidedPB INJECTIVE-COMPOSITION
//! (`injcomp`) class via a layered Hall/cardinality lower-bound paired with a
//! re-verified constructive upper bound (mirrors `clique_coloring.rs` (clique ==
//! colouring), `bipartite_vertex_cover.rs` (König), `dominating_set.rs`
//! (2-packing)).
//!
//! # The class (what the OPB actually encodes)
//!
//! Each `normalized-injcomp_opt_<L>layers_<obj>_lastlayer<r>_size_<n>.opb`
//! instance is, after decoding its normalized positional layout, an injective
//! composition of partial maps along a LAYERED bipartite chain
//! `L0 -> L1 -> ... -> L_{k-1}`  (`k = 3` or `4` node layers, so `k-1` edge
//! matrices). Intermediate layers all have `n` nodes; the LAST layer has
//! `m` nodes (`m = n-1` for `lastlayerdecr1`, `m = floor(n/2)` for
//! `lastlayerdiv2`), so `m < n`.
//!
//! Variables (the file's fixed positional blocks), with all matrices row-major
//! and 1-indexed:
//! * `M1(i,j)`  `L0 -> L1`, an `n x n` 0/1 matrix.
//! * `M2(i,j)`  `L1 -> L2`, `n x s2` (`s2 = m` for `k=3`, `s2 = n` for `k=4`).
//! * `C2(i,j)`  the composition `L0..->L2`, `n x s2` (OBJECTIVE-counted).
//! * `I1(i)`    `n` indicators: "L1 node `i` is the target of some `M1` edge".
//! * [`k=4` only] `M3(i,j)` `L2 -> L3` `n x m`, `C3(i,j)` composition `n x m`
//!   (OBJECTIVE-counted), `I2(i)` `n` indicators for L2.
//!
//! Constraint families (`>=` form; the canonical multiset is rebuilt and matched
//! exactly in [`detect`]):
//! * **colInj(M1)** `-sum_i M1(i,j) >= -1`          — each L1 node <= 1 source.
//! * **ind1**       `n*I1(j) - sum_i M1(i,j) >= 0`  — `I1(j)=1` if L1 node used.
//! * **rowImpl(M2)** `-I1(i) + sum_j M2(i,j) >= 0`  — used L1 node maps forward.
//! * **and(C2)**    `C2(i,j) - I1(i) - M2(i,j) >= -1` — `C2 >= I1 AND M2`.
//! * **colInj(C2)** `-sum_i C2(i,j) >= -1`          — composition is injective.
//! * [`k=4`] **ind2** `n*I2(j) - sum_i M2(i,j) >= 0`, **rowImpl(M3)**
//!   `-I2(i) + sum_j M3(i,j) >= 0`, **and(C3)** `C3(i,j)-I2(i)-M3(i,j) >= -1`,
//!   **colInj(C3)** `-sum_i C3(i,j) >= -1`.
//!
//! Objective: `min sum -1 * (counted vars)`.
//! * `maxfirst`: counts only `M1`            -> maximise `#M1 edges`.
//! * `maxall`  : counts `M1` and every `C_t` -> maximise edges at ALL layers.
//!
//! # Why the optimum is exact (the Hall/cardinality witness pair)
//!
//! Write `B` for the maximum of the counted sum; the minimisation optimum is
//! `-B`.
//!
//! **(a) Each composition layer is capped by its target size.** `C_t` is
//! injective: summing its `s_t` column rows `-sum_i C_t(i,j) >= -1` gives
//! `sum C_t <= s_t`. So `C2 <= s2`, and (`k=4`) `C3 <= s3 = m`. (A direct
//! Farkas sum of the column rows.)
//!
//! **(b) `sum M1 <= m` (the layered Hall bound).** `M1` is injective, so
//! `sum M1` equals the number `a` of "active" L1 columns (columns with an
//! edge). Each active column `i`: by **ind1** forces `I1(i)=1`; by **rowImpl**
//! forces some `M2(i,j)=1`; by **and(C2)** forces `C2(i,j)=1` — a REAL `M2`
//! edge into L2 column `j`. By **colInj(C2)** distinct active `i` occupy
//! distinct L2 columns, and each such column has a genuine `M2` edge, so by
//! **ind2** it is L2-active, by **rowImpl(M3)/and(C3)** forces a `C3` edge, and
//! by **colInj(C3)** distinct L2 columns occupy distinct L3 columns. Hence the
//! active L1 columns inject all the way into the `m`-node final layer:
//! `a <= m`. (For `k=3` the chain stops one step earlier at the final `C2`
//! whose target IS the `m`-layer, giving `a <= m` directly.) So `sum M1 <= m`.
//!
//! Combining: `maxfirst` -> `B = m`; `maxall, k=3` -> `B = m + s2 = 2m`;
//! `maxall, k=4` -> `B = m + s2 + s3 = m + n + m = n + 2m`.
//!
//! **Tightness (UB witness).** The diagonal assignment `M1(i,i)=M2(i,i)=
//! C(i,i)=1` for `i in 1..=m` (plus, for `k=4`, the analogous `M3/C3` diagonal
//! and free `C2` edges filling the remaining `s2-m` columns) is feasible and
//! attains `B`. So `-B <= opt <= -B`.
//!
//! # Why the returned value is an *optimum* (sound regardless of bugs here)
//!
//! [`try_solve`] returns `OptimumFound` ONLY when three independently
//! re-checkable facts hold, so a false optimum is impossible by construction:
//!
//! 1. **Exact structural match (LB witness).** [`detect`] rebuilds the canonical
//!    constraint multiset AND the objective for the recovered `(n, m, k,
//!    maxfirst)` and requires the instance to equal them EXACTLY (every family
//!    present, none missing/extra) with the exact variable count. Only under
//!    this match do the theorem's hypotheses hold, giving `opt >= -B`. A missing
//!    constraint (which could deepen the true optimum) breaks the match and we
//!    decline.
//! 2. **Feasible construction (UB witness).** The diagonal assignment is
//!    re-verified against the ORIGINAL constraints with `verify_all_constraints`,
//!    so `opt <= eval_objective(assignment)`.
//! 3. **Witnesses meet.** `eval_objective(assignment) == -B`.
//!
//! `-B <= opt <= eval_objective == -B` forces equality. A bug in detection or
//! construction simply fails a check and we return `None` (fall through to the
//! general portfolio; incumbent stays SATISFIABLE). 0-wrong by construction.

use std::collections::HashMap;

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// Fail-closed size guards (canonical rebuild is linear in these).
const MAX_VARS: usize = 8_000_000;
const MAX_CONS: usize = 8_000_000;

/// A detected injcomp instance: recovered family parameters and the positional
/// variable layout. Variable ids are 1-indexed throughout.
struct InjCompShape {
    /// Size of every intermediate layer (`L0..L_{k-1}`).
    n: usize,
    /// Size of the final layer.
    m: usize,
    /// Number of node layers: 3 or 4.
    layers: usize,
    /// `true` => objective counts only `M1` (`maxfirst`); `false` => `maxall`.
    maxfirst: bool,
}

impl InjCompShape {
    /// Size of `L2` (the target of `M2`/`C2`): `m` for `k=3`, `n` for `k=4`.
    fn s2(&self) -> usize {
        if self.layers == 3 {
            self.m
        } else {
            self.n
        }
    }

    // --- positional variable accessors (all return 1-indexed var ids) ---
    // Layout (k=3): M1[n*n] M2[n*m] C2[n*m] I1[n].
    // Layout (k=4): M1[n*n] M2[n*n] C2[n*n] I1[n] M3[n*m] C3[n*m] I2[n].

    fn m1(&self, i: usize, j: usize) -> usize {
        (i - 1) * self.n + j
    }
    fn m2(&self, i: usize, j: usize) -> usize {
        let s2 = self.s2();
        self.n * self.n + (i - 1) * s2 + j
    }
    fn c2(&self, i: usize, j: usize) -> usize {
        let s2 = self.s2();
        self.n * self.n + self.n * s2 + (i - 1) * s2 + j
    }
    fn i1(&self, i: usize) -> usize {
        let s2 = self.s2();
        self.n * self.n + 2 * self.n * s2 + i
    }
    // k=4-only blocks (s2 == n there).
    fn base_after_i1(&self) -> usize {
        3 * self.n * self.n + self.n
    }
    fn m3(&self, i: usize, j: usize) -> usize {
        self.base_after_i1() + (i - 1) * self.m + j
    }
    fn c3(&self, i: usize, j: usize) -> usize {
        self.base_after_i1() + self.n * self.m + (i - 1) * self.m + j
    }
    fn i2(&self, i: usize) -> usize {
        self.base_after_i1() + 2 * self.n * self.m + i
    }

    /// Total variable count implied by the layout.
    fn num_vars(&self) -> usize {
        if self.layers == 3 {
            self.n * self.n + 2 * self.n * self.m + self.n
        } else {
            3 * self.n * self.n + 2 * self.n + 2 * self.n * self.m
        }
    }

    /// The maximum of the counted objective sum (`B`); the minimisation optimum
    /// is `-B`.
    fn bound(&self) -> i128 {
        let m = self.m as i128;
        if self.maxfirst {
            m
        } else if self.layers == 3 {
            2 * m
        } else {
            self.n as i128 + 2 * m
        }
    }
}

/// Canonical, order-independent constraint signature: `(rel, rhs, sorted
/// (coeff, var))`. Two constraints are the same family member iff equal.
type ConstraintKey = (u8, i128, Vec<(i128, u32)>);

fn rel_code(rel: PbRel) -> u8 {
    match rel {
        PbRel::Ge => 0,
        PbRel::Eq => 1,
    }
}

/// Canonicalises a constraint to its signature, or `None` if it contains any
/// non-unit or negated literal (the injcomp family has neither, so such a row
/// can never match and the whole instance declines).
fn normalize(constraint: &PbConstraint) -> Option<ConstraintKey> {
    let mut pairs: Vec<(i128, u32)> = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 {
            return None;
        }
        pairs.push((term.coeff, lit.var));
    }
    pairs.sort_unstable();
    Some((rel_code(constraint.rel), constraint.rhs, pairs))
}

/// Builds a constraint signature directly from `(coeff, var)` pairs.
fn key_of(rel: u8, rhs: i128, mut pairs: Vec<(i128, u32)>) -> ConstraintKey {
    pairs.sort_unstable();
    (rel, rhs, pairs)
}

/// Heuristically infers `(n, m, layers)` from the constraint shapes. This is NOT
/// the soundness anchor — [`detect`] re-verifies the full canonical multiset, so
/// a wrong inference simply fails the exact match and declines.
fn infer_params(instance: &PbInstance) -> Option<(usize, usize, usize)> {
    let mut inj_len: Option<usize> = None; // all-(-1), rhs -1 => length n
    let mut rowimpl_lens: Vec<usize> = Vec::new(); // one -1, rest +1, rhs 0
    for c in &instance.constraints {
        if c.rel != PbRel::Ge {
            return None;
        }
        // Cheap unit/positive check (full check happens in normalize later).
        let mut neg_ones = 0usize;
        let mut plus_ones = 0usize;
        let mut other = 0usize;
        for t in &c.terms {
            if t.lits.len() != 1 || t.lits[0].negated {
                return None;
            }
            match t.coeff {
                -1 => neg_ones += 1,
                1 => plus_ones += 1,
                _ => other += 1,
            }
        }
        if c.rhs == -1 && plus_ones == 0 && other == 0 && neg_ones == c.terms.len() {
            // colInj row: length is n.
            match inj_len {
                None => inj_len = Some(c.terms.len()),
                Some(l) if l == c.terms.len() => {}
                Some(_) => return None, // non-uniform => not the class
            }
        } else if c.rhs == 0 && neg_ones == 1 && other == 0 && plus_ones == c.terms.len() - 1 {
            // rowImpl row: -ind + sum(matrix row); matrix-row length = len-1.
            rowimpl_lens.push(c.terms.len() - 1);
        }
    }
    let n = inj_len?;
    if n < 2 {
        return None;
    }
    rowimpl_lens.sort_unstable();
    rowimpl_lens.dedup();
    match rowimpl_lens.as_slice() {
        [m] => {
            // 3 layers: final composition row length is m.
            if *m >= 1 && *m < n {
                Some((n, *m, 3))
            } else {
                None
            }
        }
        [m, big] => {
            // 4 layers: intermediate rows length n, final rows length m.
            if *big == n && *m >= 1 && *m < n {
                Some((n, *m, 4))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Recognises the injcomp class and recovers the [`InjCompShape`], but ONLY after
/// verifying that the instance's constraint multiset AND objective equal the
/// canonical family for the recovered parameters EXACTLY. Returns `None` for
/// anything that is not precisely this shape (intentionally strict).
fn detect(instance: &PbInstance, objective: &PbObjective) -> Option<InjCompShape> {
    let num_vars = instance.num_vars as usize;
    if num_vars == 0 || num_vars > MAX_VARS || instance.constraints.len() > MAX_CONS {
        return None;
    }
    let (n, m, layers) = infer_params(instance)?;

    // Objective length distinguishes maxfirst (only M1) from maxall.
    let obj_len = objective.terms.len();
    let maxfirst = obj_len == n * n;
    let shape = InjCompShape {
        n,
        m,
        layers,
        maxfirst,
    };
    if shape.num_vars() != num_vars {
        return None;
    }

    // --- Rebuild the canonical objective and require an exact multiset match. ---
    let mut obj_canon: HashMap<(i128, u32), i64> = HashMap::new();
    let mut obj_add = |coeff: i128, var: usize| {
        *obj_canon.entry((coeff, var as u32)).or_insert(0) += 1;
    };
    for i in 1..=n {
        for j in 1..=n {
            obj_add(-1, shape.m1(i, j));
        }
    }
    if !maxfirst {
        let s2 = shape.s2();
        for i in 1..=n {
            for j in 1..=s2 {
                obj_add(-1, shape.c2(i, j));
            }
        }
        if layers == 4 {
            for i in 1..=n {
                for j in 1..=m {
                    obj_add(-1, shape.c3(i, j));
                }
            }
        }
    }
    for term in &objective.terms {
        if term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 {
            return None;
        }
        match obj_canon.get_mut(&(term.coeff, lit.var)) {
            Some(count) if *count > 0 => *count -= 1,
            _ => return None,
        }
    }
    if obj_canon.values().any(|&c| c != 0) {
        return None;
    }

    // --- Rebuild the canonical constraint multiset and consume the instance. ---
    let mut canon: HashMap<ConstraintKey, i64> = HashMap::new();
    let mut add = |key: ConstraintKey| {
        *canon.entry(key).or_insert(0) += 1;
    };
    let s2 = shape.s2();
    let ge = rel_code(PbRel::Ge);

    // colInj(M1): -sum_i M1(i,j) >= -1.
    for j in 1..=n {
        let pairs: Vec<(i128, u32)> = (1..=n).map(|i| (-1, shape.m1(i, j) as u32)).collect();
        add(key_of(ge, -1, pairs));
    }
    // ind1: n*I1(j) - sum_i M1(i,j) >= 0.
    for j in 1..=n {
        let mut pairs: Vec<(i128, u32)> = Vec::with_capacity(n + 1);
        pairs.push((n as i128, shape.i1(j) as u32));
        for i in 1..=n {
            pairs.push((-1, shape.m1(i, j) as u32));
        }
        add(key_of(ge, 0, pairs));
    }
    // rowImpl(M2): -I1(i) + sum_j M2(i,j) >= 0.
    for i in 1..=n {
        let mut pairs: Vec<(i128, u32)> = Vec::with_capacity(s2 + 1);
        pairs.push((-1, shape.i1(i) as u32));
        for j in 1..=s2 {
            pairs.push((1, shape.m2(i, j) as u32));
        }
        add(key_of(ge, 0, pairs));
    }
    // and(C2): C2(i,j) - I1(i) - M2(i,j) >= -1.
    for i in 1..=n {
        for j in 1..=s2 {
            let pairs = vec![
                (1i128, shape.c2(i, j) as u32),
                (-1, shape.i1(i) as u32),
                (-1, shape.m2(i, j) as u32),
            ];
            add(key_of(ge, -1, pairs));
        }
    }
    // colInj(C2): -sum_i C2(i,j) >= -1.
    for j in 1..=s2 {
        let pairs: Vec<(i128, u32)> = (1..=n).map(|i| (-1, shape.c2(i, j) as u32)).collect();
        add(key_of(ge, -1, pairs));
    }
    if layers == 4 {
        // ind2: n*I2(j) - sum_i M2(i,j) >= 0.
        for j in 1..=n {
            let mut pairs: Vec<(i128, u32)> = Vec::with_capacity(n + 1);
            pairs.push((n as i128, shape.i2(j) as u32));
            for i in 1..=n {
                pairs.push((-1, shape.m2(i, j) as u32));
            }
            add(key_of(ge, 0, pairs));
        }
        // rowImpl(M3): -I2(i) + sum_j M3(i,j) >= 0.
        for i in 1..=n {
            let mut pairs: Vec<(i128, u32)> = Vec::with_capacity(m + 1);
            pairs.push((-1, shape.i2(i) as u32));
            for j in 1..=m {
                pairs.push((1, shape.m3(i, j) as u32));
            }
            add(key_of(ge, 0, pairs));
        }
        // and(C3): C3(i,j) - I2(i) - M3(i,j) >= -1.
        for i in 1..=n {
            for j in 1..=m {
                let pairs = vec![
                    (1i128, shape.c3(i, j) as u32),
                    (-1, shape.i2(i) as u32),
                    (-1, shape.m3(i, j) as u32),
                ];
                add(key_of(ge, -1, pairs));
            }
        }
        // colInj(C3): -sum_i C3(i,j) >= -1.
        for j in 1..=m {
            let pairs: Vec<(i128, u32)> = (1..=n).map(|i| (-1, shape.c3(i, j) as u32)).collect();
            add(key_of(ge, -1, pairs));
        }
    }

    // Length must match before consuming (so "every instance row hits a distinct
    // canonical slot" + equal totals => the multisets coincide).
    let expected: i64 = canon.values().sum();
    if instance.constraints.len() as i64 != expected {
        return None;
    }
    for constraint in &instance.constraints {
        let key = normalize(constraint)?;
        match canon.get_mut(&key) {
            Some(count) if *count > 0 => *count -= 1,
            _ => return None,
        }
    }
    if canon.values().any(|&c| c != 0) {
        return None;
    }

    Some(shape)
}

/// Constructs the diagonal UB assignment that attains `B` (see module docs).
///
/// The FULL layered chain is always built (so every constraint is satisfied,
/// independent of which vars the objective counts): the diagonal gives `M1 = m`
/// (the `maxfirst` optimum), and the composition diagonals + free `C2` fill give
/// `C2 = s2`, `C3 = m` (the extra `maxall` terms). For `maxfirst` the composition
/// vars are simply not counted by the objective, but they are still set so the
/// downstream `ind2`/`rowImpl`/`and`/`colInj` rows hold.
fn construct_ub(shape: &InjCompShape) -> Vec<bool> {
    let num_vars = shape.num_vars();
    let mut a = vec![false; num_vars];
    let mut set = |var: usize| {
        if var >= 1 && var <= num_vars {
            a[var - 1] = true;
        }
    };
    let m = shape.m;
    let s2 = shape.s2();
    // Diagonal up to m: M1(i,i)=M2(i,i)=C2(i,i)=1, I1(i)=1.
    for i in 1..=m {
        set(shape.m1(i, i));
        set(shape.i1(i));
        set(shape.m2(i, i));
        set(shape.c2(i, i));
    }
    // Fill C2 to its full s2 columns (free composition edges, capped only by
    // colInj) so C2 = s2. For 3 layers s2 == m and the diagonal already fills
    // every column, so this loop is empty.
    for j in (m + 1)..=s2 {
        set(shape.c2(1, j));
    }
    if shape.layers == 4 {
        // L2 columns 1..=m are used by M2(i,i): drive their indicators (required
        // by ind2) + the M3/C3 diagonal (required by rowImpl(M3)) so C3 = m.
        for i in 1..=m {
            set(shape.i2(i));
            set(shape.m3(i, i));
            set(shape.c3(i, i));
        }
    }
    a
}

/// Attempts to solve `instance` as an injcomp certified optimum, returning a
/// re-verified `OptimumFound` solution or `None`.
pub(crate) fn try_solve(instance: &PbInstance, objective: &PbObjective) -> Option<PbSolution> {
    let shape = detect(instance, objective)?;

    // --- UB witness. ---
    let assignment = construct_ub(&shape);
    // 2. Feasible against the ORIGINAL constraints -> valid upper bound.
    if !verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    // 1 + 3. The exact structural match in `detect` established the Hall/cardinality
    // lower bound `opt >= -B`; require the UB to meet it exactly.
    let lower_bound = -shape.bound();
    let value = eval_objective(objective, &assignment);
    if value != lower_bound {
        return None;
    }

    Some(PbSolution {
        status: PbStatus::OptimumFound,
        assignment,
        objective: Some(value),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbObjective, PbTerm};

    fn pos(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![pos(var)],
        }
    }

    /// Builds the canonical injcomp OPB for `(n, m, layers, maxfirst)` exactly as
    /// the normalized instances are laid out. Ground truth for the recogniser and
    /// the brute-force cross-check.
    fn canonical_instance(
        n: usize,
        m: usize,
        layers: usize,
        maxfirst: bool,
    ) -> (PbInstance, PbObjective) {
        let shape = InjCompShape {
            n,
            m,
            layers,
            maxfirst,
        };
        let s2 = shape.s2();
        let mut cons: Vec<PbConstraint> = Vec::new();
        let ge = PbRel::Ge;
        // colInj(M1)
        for j in 1..=n {
            cons.push(PbConstraint {
                terms: (1..=n).map(|i| term(-1, shape.m1(i, j) as u32)).collect(),
                rel: ge,
                rhs: -1,
            });
        }
        // ind1
        for j in 1..=n {
            let mut terms = vec![term(n as i128, shape.i1(j) as u32)];
            for i in 1..=n {
                terms.push(term(-1, shape.m1(i, j) as u32));
            }
            cons.push(PbConstraint {
                terms,
                rel: ge,
                rhs: 0,
            });
        }
        // rowImpl(M2)
        for i in 1..=n {
            let mut terms = vec![term(-1, shape.i1(i) as u32)];
            for j in 1..=s2 {
                terms.push(term(1, shape.m2(i, j) as u32));
            }
            cons.push(PbConstraint {
                terms,
                rel: ge,
                rhs: 0,
            });
        }
        // and(C2)
        for i in 1..=n {
            for j in 1..=s2 {
                cons.push(PbConstraint {
                    terms: vec![
                        term(1, shape.c2(i, j) as u32),
                        term(-1, shape.i1(i) as u32),
                        term(-1, shape.m2(i, j) as u32),
                    ],
                    rel: ge,
                    rhs: -1,
                });
            }
        }
        // colInj(C2)
        for j in 1..=s2 {
            cons.push(PbConstraint {
                terms: (1..=n).map(|i| term(-1, shape.c2(i, j) as u32)).collect(),
                rel: ge,
                rhs: -1,
            });
        }
        if layers == 4 {
            // ind2
            for j in 1..=n {
                let mut terms = vec![term(n as i128, shape.i2(j) as u32)];
                for i in 1..=n {
                    terms.push(term(-1, shape.m2(i, j) as u32));
                }
                cons.push(PbConstraint {
                    terms,
                    rel: ge,
                    rhs: 0,
                });
            }
            // rowImpl(M3)
            for i in 1..=n {
                let mut terms = vec![term(-1, shape.i2(i) as u32)];
                for j in 1..=m {
                    terms.push(term(1, shape.m3(i, j) as u32));
                }
                cons.push(PbConstraint {
                    terms,
                    rel: ge,
                    rhs: 0,
                });
            }
            // and(C3)
            for i in 1..=n {
                for j in 1..=m {
                    cons.push(PbConstraint {
                        terms: vec![
                            term(1, shape.c3(i, j) as u32),
                            term(-1, shape.i2(i) as u32),
                            term(-1, shape.m3(i, j) as u32),
                        ],
                        rel: ge,
                        rhs: -1,
                    });
                }
            }
            // colInj(C3)
            for j in 1..=m {
                cons.push(PbConstraint {
                    terms: (1..=n).map(|i| term(-1, shape.c3(i, j) as u32)).collect(),
                    rel: ge,
                    rhs: -1,
                });
            }
        }
        let mut obj_terms: Vec<PbTerm> = Vec::new();
        for i in 1..=n {
            for j in 1..=n {
                obj_terms.push(term(-1, shape.m1(i, j) as u32));
            }
        }
        if !maxfirst {
            for i in 1..=n {
                for j in 1..=s2 {
                    obj_terms.push(term(-1, shape.c2(i, j) as u32));
                }
            }
            if layers == 4 {
                for i in 1..=n {
                    for j in 1..=m {
                        obj_terms.push(term(-1, shape.c3(i, j) as u32));
                    }
                }
            }
        }
        let objective = PbObjective { terms: obj_terms };
        let num_vars = shape.num_vars() as u32;
        let instance = PbInstance {
            num_vars,
            num_constraints: cons.len() as u32,
            constraints: cons,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    /// Brute-force the true optimum over all `2^num_vars` assignments (tiny only).
    fn brute_force_opt(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
        let nv = instance.num_vars as usize;
        assert!(nv <= 22, "brute force only for tiny instances");
        let mut best: Option<i128> = None;
        for mask in 0u32..(1u32 << nv) {
            let a: Vec<bool> = (0..nv).map(|v| (mask >> v) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &a) {
                let val = eval_objective(objective, &a);
                best = Some(best.map_or(val, |b| b.min(val)));
            }
        }
        best
    }

    #[test]
    fn detect_recovers_parameters_3layer() {
        let (inst, obj) = canonical_instance(12, 11, 3, false);
        let shape = detect(&inst, &obj).expect("3layer detected");
        assert_eq!(
            (shape.n, shape.m, shape.layers, shape.maxfirst),
            (12, 11, 3, false)
        );
        assert_eq!(shape.bound(), 22);
    }

    #[test]
    fn detect_recovers_parameters_4layer() {
        // The flagged corpus instance: 4layers div2 size16 (n=16, m=8).
        let (inst, obj) = canonical_instance(16, 8, 4, false);
        let shape = detect(&inst, &obj).expect("4layer detected");
        assert_eq!(
            (shape.n, shape.m, shape.layers, shape.maxfirst),
            (16, 8, 4, false)
        );
        assert_eq!(shape.bound(), 32); // n + 2m = 16 + 16
    }

    #[test]
    fn detect_recovers_maxfirst() {
        let (inst, obj) = canonical_instance(18, 17, 3, true);
        let shape = detect(&inst, &obj).expect("maxfirst detected");
        assert!(shape.maxfirst);
        assert_eq!(shape.bound(), 17); // m
    }

    #[test]
    fn certifies_3layer_maxall() {
        // Mirrors normalized-...3layers_maxall_lastlayerdecr1_size_12 (opt -22).
        let (inst, obj) = canonical_instance(12, 11, 3, false);
        let sol = try_solve(&inst, &obj).expect("certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(-22));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn certifies_4layer_maxall_flagged_family() {
        // Mirrors the flagged normalized-...4layers_maxall_lastlayerdiv2_size_16
        // (incumbent SAT -32 -> certified OPTIMUM -32).
        let (inst, obj) = canonical_instance(16, 8, 4, false);
        let sol = try_solve(&inst, &obj).expect("certifies");
        assert_eq!(sol.objective, Some(-32));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn certifies_maxfirst() {
        let (inst, obj) = canonical_instance(31, 15, 3, true);
        let sol = try_solve(&inst, &obj).expect("certifies");
        assert_eq!(sol.objective, Some(-15));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn brute_force_cross_check_3layer_n2_m1() {
        // 4 + 4 + 2 = 10 vars. maxall opt = -2m = -2.
        let (inst, obj) = canonical_instance(2, 1, 3, false);
        let sol = try_solve(&inst, &obj).expect("certifies");
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, -2);
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_3layer_n3_m1() {
        // 9 + 6 + 3 = 18 vars. maxall opt = -2m = -2.
        let (inst, obj) = canonical_instance(3, 1, 3, false);
        let sol = try_solve(&inst, &obj).expect("certifies");
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, -2);
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_3layer_n3_m1_maxfirst() {
        let (inst, obj) = canonical_instance(3, 1, 3, true);
        let sol = try_solve(&inst, &obj).expect("certifies");
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, -1); // m
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_4layer_n2_m1() {
        // 3*4 + 4 + 4 = 20 vars. maxall opt = -(n + 2m) = -(2 + 2) = -4.
        let (inst, obj) = canonical_instance(2, 1, 4, false);
        let sol = try_solve(&inst, &obj).expect("certifies");
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, -4);
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_4layer_n2_m1_maxfirst() {
        let (inst, obj) = canonical_instance(2, 1, 4, true);
        let sol = try_solve(&inst, &obj).expect("certifies");
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, -1); // m
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn missing_constraint_declines() {
        // Drop one colInj(C2) row: the Hall LB hypotheses fail -> must DECLINE
        // (no unproven optimum).
        let (mut inst, obj) = canonical_instance(3, 1, 3, false);
        let p = inst
            .constraints
            .iter()
            .rposition(|c| c.rhs == -1 && c.terms.iter().all(|t| t.coeff == -1))
            .expect("has a colInj row");
        inst.constraints.remove(p);
        inst.num_constraints -= 1;
        assert!(detect(&inst, &obj).is_none());
        assert!(try_solve(&inst, &obj).is_none());
    }

    #[test]
    fn extra_constraint_declines() {
        let (mut inst, obj) = canonical_instance(3, 1, 3, false);
        inst.constraints.push(PbConstraint {
            terms: vec![term(1, 1)],
            rel: PbRel::Ge,
            rhs: 0,
        });
        inst.num_constraints += 1;
        assert!(detect(&inst, &obj).is_none());
    }

    #[test]
    fn perturbed_rhs_declines() {
        // Flip a single rhs: no longer the canonical family -> decline.
        let (mut inst, obj) = canonical_instance(3, 1, 3, false);
        let p = inst
            .constraints
            .iter()
            .position(|c| c.rhs == 0)
            .expect("has rhs0");
        inst.constraints[p].rhs = 1;
        assert!(detect(&inst, &obj).is_none());
    }

    #[test]
    fn unrelated_instance_declines() {
        let constraints = vec![
            PbConstraint {
                terms: vec![term(1, 1), term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            },
            PbConstraint {
                terms: vec![term(1, 2), term(1, 3)],
                rel: PbRel::Ge,
                rhs: 1,
            },
        ];
        let objective = PbObjective {
            terms: vec![term(1, 1), term(1, 2), term(1, 3)],
        };
        let inst = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(try_solve(&inst, &objective).is_none());
    }

    #[test]
    fn family_values_match_formula() {
        // Every real corpus parameter set certifies to its formula value.
        let cases = [
            (12, 11, 3, false, -22),
            (29, 28, 3, false, -56),
            (20, 10, 3, false, -20),
            (22, 11, 3, false, -22),
            (18, 17, 3, true, -17),
            (31, 15, 3, true, -15),
            (60, 30, 3, true, -30),
            (26, 25, 4, false, -76),
            (16, 8, 4, false, -32),
            (30, 29, 4, true, -29),
            (32, 16, 4, true, -16),
        ];
        for (n, m, layers, maxfirst, expected) in cases {
            let (inst, obj) = canonical_instance(n, m, layers, maxfirst);
            let sol = try_solve(&inst, &obj).expect("certifies");
            assert_eq!(
                sol.objective,
                Some(expected),
                "n={n} m={m} L={layers} mf={maxfirst}"
            );
            assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        }
    }
}
