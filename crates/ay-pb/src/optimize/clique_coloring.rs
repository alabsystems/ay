// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact certified optimum for the IHALAINEN PBO-CLIQUE-COLORING class via a
//! clique lower-bound / coloring upper-bound witness pair, with a self-certifying
//! soundness gate (mirrors `bipartite_vertex_cover.rs` (König) and
//! `dominating_set.rs` (2-packing)).
//!
//! # The class (what the OPB actually encodes)
//!
//! Each `normalized-clique-coloring-max-clique-n=N-t=T.opb` instance is, after
//! decoding its normalized shape, the following combinatorial optimisation on
//! `n` "nodes" with `n` first-stage colour slots and `t` second-stage colours:
//!
//! Variables (in the file's fixed positional layout):
//! * `edge(a,b)` for every pair `a<b`         — `C(n,2)` vars, ids `1..C`.
//! * `obj(i)` for `i in 1..n`                  — `n` vars, the OBJECTIVE literals.
//! * `g1(b,s)` block `b` picks slot `s`        — `n*n` vars (first grouping).
//! * `g2(b,k)` block `b` picks colour `k`      — `n*t` vars (second grouping).
//!
//! Constraint families:
//! * **A (slot cover)** `obj(i) + sum_b g1(b,i) >= 1` — if slot `i` is used by no
//!   block, its objective indicator `obj(i)` is forced to 1.
//! * **B (one slot/block)** `sum_s g1(b,s) <= 1` — each block picks <=1 slot.
//! * **C (difference forcing)** `edge(a,b) >= g1(a,p) + g1(b,q) - 1` for every
//!   `p != q` — the edge between two blocks is forced on when they pick DIFFERENT
//!   slots. So `G` = the graph whose edges join blocks of differing slots.
//! * **D (>=1 colour/block)** `sum_k g2(b,k) >= 1` — every block gets a colour.
//! * **E (proper colouring)** `edge(a,b) + g2(a,k) + g2(b,k) <= 2` for every
//!   colour `k` — adjacent blocks (active edge) may not share a `g2` colour, i.e.
//!   `g2` is a proper `t`-colouring of `G`.
//!
//! Objective: `min sum_i obj(i)` = `n - (#distinct slots used in the first
//! grouping)`. Minimising the objective therefore MAXIMISES the number of
//! distinct slots used, subject to `G` being `t`-colourable.
//!
//! # Why the optimum is exactly `n - t` (clique == colouring)
//!
//! Let a feasible assignment use `p` distinct first-grouping slots. Pick one
//! representative block per used slot (well-defined: by **B** a block picks <=1
//! slot, so distinct slots have distinct representatives). Any two
//! representatives pick different slots, so by **C** their `edge` is forced on;
//! by **E** they then take disjoint `g2` colours, and by **D** each takes
//! >=1 of the `t` colours. Pairwise-disjoint non-empty colour sets inside `t`
//! colours force `p <= t`. Hence the representatives are a CLIQUE of size `p` in
//! `G` that the second grouping properly `t`-colours, so `p <= t` (clique
//! number <= chromatic capacity). By **A**, `obj >= n - p >= n - t`: the clique
//! bound IS the lower bound.
//!
//! Conversely the colouring upper bound: assign block `b` the slot/colour
//! `((b-1) mod t) + 1`. Exactly slots `1..t` are used (`G` becomes complete
//! `t`-partite, properly `t`-coloured by the same map), so `obj = n - t`. The
//! two witnesses meet: `n - t <= opt <= n - t`, optimum `= n - t`.
//!
//! # Why the returned value is an *optimum* (sound regardless of bugs here)
//!
//! `try_solve` returns `OptimumFound` ONLY when three independently re-checkable
//! facts hold, so a false optimum is impossible by construction:
//!
//! 1. **Exact structural match (LB witness).** The instance's constraint
//!    multiset is verified to equal, exactly, the canonical clique-coloring
//!    family for the recovered `(n,t)` (every A/B/C/D/E constraint present, none
//!    missing, none extra). Only under this exact match does the clique==colouring
//!    theorem above apply, giving `opt >= n - t`. A missing forcing/colouring
//!    constraint (which could lower the true optimum) breaks the match and we
//!    decline; an extra constraint can only raise the optimum and is also caught.
//! 2. **Feasible colouring (UB witness).** The constructed `((b-1) mod t)+1`
//!    assignment is re-verified against the ORIGINAL constraints with
//!    `verify_all_constraints`, so `opt <= eval_objective(assignment)`.
//! 3. **Witnesses meet.** `eval_objective(assignment) == n - t`.
//!
//! `n - t <= opt <= eval_objective(assignment) == n - t` forces equality. None of
//! this trusts a closed-form blindly: a bug in detection or construction simply
//! fails one of the three checks and we return `None` (fall through to the
//! general portfolio, incumbent stays SATISFIABLE). 0-wrong by construction.

use std::collections::HashMap;

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// A detected clique-coloring instance: the recovered family parameters and the
/// positional variable layout. All offsets are 0-based into the `[0, num_vars)`
/// assignment vector (i.e. `var_id - 1`).
struct CliqueColoringShape {
    /// Number of nodes / first-grouping slots / objective indicators.
    n: usize,
    /// Number of second-grouping colours.
    t: usize,
    /// First variable id (1-indexed) of the objective indicators block.
    base_obj: usize,
    /// First variable id (1-indexed) minus 1 of the `g1` block (so
    /// `g1(b,s) = base_g1 + n*(b-1) + s`).
    base_g1: usize,
    /// `g2(b,k) = base_g2 + t*(b-1) + k`.
    base_g2: usize,
}

impl CliqueColoringShape {
    /// 1-indexed variable id of the lexicographic edge between blocks `a < b`
    /// (`a, b` in `1..=n`).
    fn edge_var(&self, a: usize, b: usize) -> usize {
        debug_assert!(1 <= a && a < b && b <= self.n);
        // Edges in lexicographic order: (1,2),(1,3),...,(1,n),(2,3),...
        (a - 1) * self.n - (a - 1) * a / 2 + (b - a)
    }
    /// 1-indexed variable id of objective indicator `i` (`i` in `1..=n`).
    fn obj_var(&self, i: usize) -> usize {
        self.base_obj + i
    }
    /// 1-indexed variable id of `g1(b,s)` (`b,s` in `1..=n`).
    fn g1_var(&self, b: usize, s: usize) -> usize {
        self.base_g1 + self.n * (b - 1) + s
    }
    /// 1-indexed variable id of `g2(b,k)` (`b` in `1..=n`, `k` in `1..=t`).
    fn g2_var(&self, b: usize, k: usize) -> usize {
        self.base_g2 + self.t * (b - 1) + k
    }
}

/// Canonical, order-independent signature of a constraint: relation, rhs, and the
/// sorted `(coeff, var)` pairs. Two constraints are the SAME family member iff
/// their signatures are equal (term order in the file is irrelevant).
type ConstraintKey = (u8, i128, Vec<(i128, u32)>);

fn rel_code(rel: PbRel) -> u8 {
    match rel {
        PbRel::Ge => 0,
        PbRel::Eq => 1,
    }
}

/// Normalises a constraint to its canonical signature, or `None` if it contains
/// any non-unit or negated literal (the canonical family has neither — such a
/// constraint can never match, so the whole instance declines).
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

/// Recognises the clique-coloring class and recovers `(n, t)` plus the variable
/// layout, but ONLY after verifying the instance's constraint multiset equals the
/// canonical family EXACTLY. Returns `None` for anything that is not precisely
/// this shape (detection is intentionally strict — a mismatch costs only the scan
/// and falls through to the portfolio).
fn detect(instance: &PbInstance, objective: &PbObjective) -> Option<CliqueColoringShape> {
    let num_vars = instance.num_vars as usize;
    let n = objective.terms.len();
    if n < 2 || num_vars == 0 {
        return None;
    }

    // Objective: exactly `n` positive unit terms of coeff 1 on the CONTIGUOUS
    // block of ids `C+1 ..= C+n` (the family's objective-indicator layout).
    let c = n * (n - 1) / 2; // C(n,2)
    let base_obj = c;
    let mut seen_obj = vec![false; n];
    for term in &objective.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated {
            return None;
        }
        let v = lit.var as usize;
        if v <= base_obj || v > base_obj + n {
            return None;
        }
        let idx = v - base_obj - 1;
        if seen_obj[idx] {
            return None; // repeated objective variable
        }
        seen_obj[idx] = true;
    }

    // Recover `t` from the variable count: num_vars = C + n + n*n + n*t.
    // `c + n + n*n` matches that documented shape exactly — not a `c*n` typo.
    #[allow(clippy::suspicious_operation_groupings)]
    let fixed = c + n + n * n;
    if num_vars < fixed + n {
        return None;
    }
    let rem = num_vars - fixed;
    if !rem.is_multiple_of(n) {
        return None;
    }
    let t = rem / n;
    if t == 0 {
        return None;
    }

    // `base_g2 = c + n + n*n` follows the documented variable layout
    // `num_vars = C + n + n*n + n*t` — not a `c*n` typo.
    #[allow(clippy::suspicious_operation_groupings)]
    let shape = CliqueColoringShape {
        n,
        t,
        base_obj,
        base_g1: c + n,
        base_g2: c + n + n * n,
    };

    // Expected total constraint count for this family.
    // |A|=n, |B|=n, |D|=n, |C|=C(n,2)*n*(n-1), |E|=C(n,2)*t.
    let expected_ncons = 3 * n + c * n * (n - 1) + c * t;
    if instance.constraints.len() != expected_ncons {
        return None;
    }

    // Build the canonical multiset of constraint signatures, then consume the
    // instance's constraints against it. Exact equality <=> the instance IS the
    // canonical clique-coloring family (the LB theorem's hypotheses), proven here
    // and not merely assumed.
    let mut canon: HashMap<ConstraintKey, i64> = HashMap::with_capacity(expected_ncons * 2);
    let mut add = |key: ConstraintKey| {
        *canon.entry(key).or_insert(0) += 1;
    };

    // A (slot cover): obj(i) + sum_b g1(b,i) >= 1.
    for i in 1..=n {
        let mut pairs = Vec::with_capacity(n + 1);
        pairs.push((1i128, shape.obj_var(i) as u32));
        for b in 1..=n {
            pairs.push((1i128, shape.g1_var(b, i) as u32));
        }
        add(key_of(rel_code(PbRel::Ge), 1, pairs));
    }
    // B (one slot per block): -sum_s g1(b,s) >= -1.
    for b in 1..=n {
        let pairs: Vec<(i128, u32)> = (1..=n)
            .map(|s| (-1i128, shape.g1_var(b, s) as u32))
            .collect();
        add(key_of(rel_code(PbRel::Ge), -1, pairs));
    }
    // C (difference forcing): edge(a,b) - g1(a,p) - g1(b,q) >= -1, for p != q.
    for a in 1..=n {
        for b in (a + 1)..=n {
            let e = shape.edge_var(a, b) as u32;
            for p in 1..=n {
                for q in 1..=n {
                    if p == q {
                        continue;
                    }
                    let pairs = vec![
                        (1i128, e),
                        (-1i128, shape.g1_var(a, p) as u32),
                        (-1i128, shape.g1_var(b, q) as u32),
                    ];
                    add(key_of(rel_code(PbRel::Ge), -1, pairs));
                }
            }
        }
    }
    // D (>=1 colour per block): sum_k g2(b,k) >= 1.
    for b in 1..=n {
        let pairs: Vec<(i128, u32)> = (1..=t)
            .map(|k| (1i128, shape.g2_var(b, k) as u32))
            .collect();
        add(key_of(rel_code(PbRel::Ge), 1, pairs));
    }
    // E (proper colouring): -edge(a,b) - g2(a,k) - g2(b,k) >= -2, for each k.
    for a in 1..=n {
        for b in (a + 1)..=n {
            let e = shape.edge_var(a, b) as u32;
            for k in 1..=t {
                let pairs = vec![
                    (-1i128, e),
                    (-1i128, shape.g2_var(a, k) as u32),
                    (-1i128, shape.g2_var(b, k) as u32),
                ];
                add(key_of(rel_code(PbRel::Ge), -2, pairs));
            }
        }
    }

    // Consume every instance constraint against the canonical multiset.
    for constraint in &instance.constraints {
        let key = normalize(constraint)?;
        match canon.get_mut(&key) {
            Some(count) if *count > 0 => *count -= 1,
            _ => return None, // unexpected / duplicate / missing-from-canonical
        }
    }
    // With exact length equality already checked and every instance constraint
    // matching a distinct canonical slot, the multisets coincide. (Defensive: no
    // canonical slot should remain.)
    if canon.values().any(|&c| c != 0) {
        return None;
    }

    Some(shape)
}

/// Attempts to solve `instance` as a clique-coloring optimum, returning a
/// certified `OptimumFound` solution or `None`.
pub(crate) fn try_solve(instance: &PbInstance, objective: &PbObjective) -> Option<PbSolution> {
    let shape = detect(instance, objective)?;
    let n = shape.n;
    let t = shape.t;
    let num_vars = instance.num_vars as usize;

    // --- UB witness: the colouring assignment using exactly `t` slots/colours.
    // Block `b` takes slot/colour s(b) = ((b-1) mod t) + 1 (in `1..=t`). ---
    let s = |b: usize| -> usize { ((b - 1) % t) + 1 };
    let mut assignment = vec![false; num_vars];
    let set = |a: &mut [bool], var: usize| {
        // `var` is 1-indexed; detection guarantees it is within range, but guard
        // defensively so a layout bug cannot index out of bounds (it would just
        // fail the feasibility re-check below).
        if var >= 1 && var <= a.len() {
            a[var - 1] = true;
        }
    };
    for a in 1..=n {
        for b in (a + 1)..=n {
            if s(a) != s(b) {
                set(&mut assignment, shape.edge_var(a, b));
            }
        }
    }
    for b in 1..=n {
        set(&mut assignment, shape.g1_var(b, s(b)));
        set(&mut assignment, shape.g2_var(b, s(b)));
    }
    for i in (t + 1)..=n {
        set(&mut assignment, shape.obj_var(i));
    }

    // --- SOUNDNESS CERTIFICATE (three independent checks) ---
    // 2. UB feasible against the ORIGINAL constraints -> valid upper bound.
    if !verify_all_constraints(&instance.constraints, &assignment) {
        return None;
    }
    // 1 + 3. The exact structural match in `detect` established the clique lower
    // bound `opt >= n - t`; require the UB to meet it exactly.
    let lower_bound = (n as i128) - (t as i128);
    let lower_bound = lower_bound.max(0);
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

    /// Builds the canonical clique-coloring OPB for `(n, t)` exactly as the
    /// normalized instances are laid out (edges, obj, g1, g2). Used by the tests
    /// as ground truth for the recogniser and the brute-force cross-check.
    fn canonical_instance(n: usize, t: usize) -> (PbInstance, PbObjective) {
        let c = n * (n - 1) / 2;
        let shape = CliqueColoringShape {
            n,
            t,
            base_obj: c,
            base_g1: c + n,
            base_g2: c + n + n * n,
        };
        let num_vars = c + n + n * n + n * t;
        let mut constraints: Vec<PbConstraint> = Vec::new();
        // A
        for i in 1..=n {
            let mut terms = vec![term(1, shape.obj_var(i) as u32)];
            for b in 1..=n {
                terms.push(term(1, shape.g1_var(b, i) as u32));
            }
            constraints.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: 1,
            });
        }
        // B
        for b in 1..=n {
            let terms = (1..=n)
                .map(|sl| term(-1, shape.g1_var(b, sl) as u32))
                .collect();
            constraints.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: -1,
            });
        }
        // C
        for a in 1..=n {
            for b in (a + 1)..=n {
                let e = shape.edge_var(a, b) as u32;
                for p in 1..=n {
                    for q in 1..=n {
                        if p == q {
                            continue;
                        }
                        constraints.push(PbConstraint {
                            terms: vec![
                                term(1, e),
                                term(-1, shape.g1_var(a, p) as u32),
                                term(-1, shape.g1_var(b, q) as u32),
                            ],
                            rel: PbRel::Ge,
                            rhs: -1,
                        });
                    }
                }
            }
        }
        // D
        for b in 1..=n {
            let terms = (1..=t)
                .map(|k| term(1, shape.g2_var(b, k) as u32))
                .collect();
            constraints.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: 1,
            });
        }
        // E
        for a in 1..=n {
            for b in (a + 1)..=n {
                let e = shape.edge_var(a, b) as u32;
                for k in 1..=t {
                    constraints.push(PbConstraint {
                        terms: vec![
                            term(-1, e),
                            term(-1, shape.g2_var(a, k) as u32),
                            term(-1, shape.g2_var(b, k) as u32),
                        ],
                        rel: PbRel::Ge,
                        rhs: -2,
                    });
                }
            }
        }
        let objective = PbObjective {
            terms: (1..=n).map(|i| term(1, shape.obj_var(i) as u32)).collect(),
        };
        let instance = PbInstance {
            num_vars: num_vars as u32,
            num_constraints: constraints.len() as u32,
            constraints,
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
    fn detect_recovers_parameters() {
        let (inst, obj) = canonical_instance(5, 3);
        let shape = detect(&inst, &obj).expect("n=5,t=3 detected");
        assert_eq!(shape.n, 5);
        assert_eq!(shape.t, 3);
    }

    #[test]
    fn n5_t3_certifies_optimum_two() {
        // Matches the real corpus instance: opt = n - t = 2.
        let (inst, obj) = canonical_instance(5, 3);
        let sol = try_solve(&inst, &obj).expect("n=5,t=3 certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(2));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn n7_t3_certifies_optimum_four() {
        // The SAT-only gap instance family member: opt = 4, which AY's heuristic
        // does not reach on its own.
        let (inst, obj) = canonical_instance(7, 3);
        let sol = try_solve(&inst, &obj).expect("n=7,t=3 certifies");
        assert_eq!(sol.objective, Some(4));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn brute_force_cross_check_n3_t1() {
        // Tiny: 3 + 3 + 9 + 3 = 18 vars. t=1 forces a single colour, so any
        // active edge is a colouring conflict -> all blocks must share one slot
        // -> opt = n - t = 2. Brute force confirms against raw OPB semantics.
        let (inst, obj) = canonical_instance(3, 1);
        let sol = try_solve(&inst, &obj).expect("n=3,t=1 certifies");
        assert_eq!(sol.objective, Some(2));
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, 2);
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_n3_t2() {
        // 3 + 3 + 9 + 6 = 21 vars. opt = n - t = 1. The clique=colouring duality:
        // two of three blocks may share a slot (so G is bipartite, 2-colourable)
        // but not all three distinct (K_3 needs 3 > t=2 colours).
        let (inst, obj) = canonical_instance(3, 2);
        let sol = try_solve(&inst, &obj).expect("n=3,t=2 certifies");
        assert_eq!(sol.objective, Some(1));
        let brute = brute_force_opt(&inst, &obj).expect("feasible");
        assert_eq!(brute, 1);
        assert_eq!(sol.objective, Some(brute));
    }

    #[test]
    fn brute_force_cross_check_n2_t1() {
        // Minimal member: 1 + 2 + 4 + 2 = 9 vars. opt = n - t = 1.
        let (inst, obj) = canonical_instance(2, 1);
        let sol = try_solve(&inst, &obj).expect("n=2,t=1 certifies");
        assert_eq!(sol.objective, Some(1));
        assert_eq!(brute_force_opt(&inst, &obj), Some(1));
    }

    #[test]
    fn missing_coloring_constraint_does_not_certify() {
        // Drop ONE family-E (proper-colouring) constraint. The instance is no
        // longer the canonical family: the clique LB theorem's hypotheses fail,
        // so detection must DECLINE rather than emit a (now unproven) optimum.
        let (mut inst, obj) = canonical_instance(3, 2);
        // Find and remove a family-E constraint (rhs == -2).
        let pos = inst
            .constraints
            .iter()
            .position(|c| c.rhs == -2)
            .expect("has an E constraint");
        inst.constraints.remove(pos);
        inst.num_constraints -= 1;
        assert!(detect(&inst, &obj).is_none());
        assert!(try_solve(&inst, &obj).is_none());
    }

    #[test]
    fn extra_constraint_does_not_certify() {
        // An EXTRA constraint (count mismatch) is rejected: the structural match
        // is exact, so even a redundant addition declines (defence in depth).
        let (mut inst, obj) = canonical_instance(3, 2);
        inst.constraints.push(PbConstraint {
            terms: vec![term(1, 1)],
            rel: PbRel::Ge,
            rhs: 0,
        });
        inst.num_constraints += 1;
        assert!(detect(&inst, &obj).is_none());
    }

    #[test]
    fn unrelated_instance_declines() {
        // A generic vertex-cover-style instance must not be mistaken for the
        // clique-coloring family.
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
    fn wrong_value_would_not_be_emitted() {
        // Sanity: the constructed colouring's objective equals n - t for a range
        // of parameters, so the `value == lower_bound` gate always passes on the
        // real family (and would decline if construction were off).
        for (n, t) in [(4usize, 2usize), (5, 3), (6, 4), (7, 3), (8, 6)] {
            let (inst, obj) = canonical_instance(n, t);
            let sol = try_solve(&inst, &obj).expect("certifies");
            assert_eq!(sol.objective, Some((n - t) as i128));
            assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        }
    }
}
