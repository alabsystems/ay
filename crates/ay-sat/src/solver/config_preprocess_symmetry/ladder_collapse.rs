// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ladder-collapse pre-pass: rewrite sequential at-most-one ladders into their
//! pairwise binary closure so the orbitope route can see the matrix structure.
//!
//! # Why this exists
//!
//! The `adv_gc` graph-colouring family encodes each vertex's at-most-one-colour
//! constraint as a Sinz sequential ladder whose colour order is SHUFFLED per
//! vertex. For base variables `x_{σ(1)}..x_{σ(k)}` and register variables
//! `s_1..s_{k-1}` the ladder is the 3k-4 clauses
//!
//! ```text
//! (¬x_{σ(1)} ∨ s_1)
//! (¬x_{σ(i)} ∨ s_i)  (¬s_{i-1} ∨ s_i)  (¬x_{σ(i)} ∨ ¬s_{i-1})   for i in 2..k
//! (¬x_{σ(k)} ∨ ¬s_{k-1})
//! ```
//!
//! (verified against the real `adv_gc_n100_k10` CNF: vertex 0 has
//! σ = [8,5,10,7,4,9,6,2,1,3] with aux 1001..1009 and exactly this shape).
//! Because every vertex uses a different σ, no colour permutation maps the
//! ladder clauses onto each other, so the orbitope detector's sound row-swap
//! gate rejects the very first transposition and the instance looks
//! symmetry-free — while being EXACTLY the row-interchangeable matrix the
//! route exists to break. Collapsing each ladder into the `C(k,2)` pairwise
//! at-most-one binaries it implies restores the syntactic symmetry: the
//! remaining formula (ALO clauses + edge clauses + pairwise AMO) is invariant
//! under colour swaps, the row-swap gate passes, and clique seeding plus the
//! orbitopal staircase close the instance at root.
//!
//! # Soundness
//!
//! * Every derived binary `(¬x_{σ(i)} ∨ ¬x_{σ(j)})`, `i < j`, is a plain RUP
//!   consequence of the ladder: `x_{σ(i)}` propagates `s_i .. s_{j-1}` up the
//!   chain and `(¬x_{σ(j)} ∨ ¬s_{j-1})` closes the conflict. Under a DRAT
//!   surface the binaries are emitted as ordinary derived additions BEFORE the
//!   ladder clauses are deleted, so the checker sees each one while its
//!   antecedents are still present.
//! * Deleting the ladder clauses afterwards only weakens the formula, so any
//!   later refutation remains valid. The register variables then occur in NO
//!   clause at all — the strict occurrence census below is what guarantees
//!   this — and are marked eliminated exactly like BVE pivots.
//! * SAT models are repaired by BVE-style witness reconstruction entries
//!   (pushed by `Solver::preprocess_symmetry_ladder_collapse`, which documents
//!   the replay-order proof): the registers are recomputed as the prefix ORs
//!   `s_i = x_{σ(1)} ∨ … ∨ x_{σ(i)}`, which satisfies every deleted clause
//!   because the surviving pairwise AMO allows at most one true base variable
//!   per ladder.
//!
//! The pass is sound standalone: it does not assume the orbitope route fires
//! afterwards.
//!
//! # Strictness
//!
//! Recognition is deliberately conservative. A register variable is accepted
//! only when EVERY occurrence is one of its ladder's clauses:
//!
//! * all occurrences are binary, root-unassigned clauses of the three ladder
//!   shapes (head `pos=1/link=1/amo=1`, middle `pos=2/link=1/amo=1`, tail
//!   `pos=2/link=0/amo=1`) — any unit, long, positive-positive, or
//!   assignment-touched occurrence disqualifies the variable;
//! * the chain walk demands the σ-pairing: step `i`'s AMO partner
//!   `(¬x ∨ ¬s_i)` must be the SAME base variable as step `i+1`'s
//!   `(¬x ∨ s_{i+1})` — a mismatched partner means the pairwise closure is NOT
//!   implied (e.g. swapping one AMO partner leaves `(¬x_1 ∨ ¬x_2)` underivable)
//!   and the whole ladder is rejected;
//! * base and register sets must be disjoint, all distinct, and the recovered
//!   clause set must have exactly `3k-4` members;
//! * across ladders: no clause is claimed twice, no register serves two
//!   ladders, and no accepted ladder's base variable is any recognized
//!   ladder's register.

use crate::literal::{Literal, Variable};
use std::collections::{BTreeMap, BTreeSet};

/// Maximum ladder width (base variables per ladder). The derived closure is
/// `k(k-1)/2` binaries versus the `3k-4` deleted clauses (~1.7x at k=10), so
/// the cap bounds the quadratic growth. `adv_gc` tops out at k=15.
pub(in crate::solver) const LADDER_COLLAPSE_MAX_WIDTH: usize = 128;
/// Minimum width worth collapsing; also rejects degenerate 2-variable chains.
pub(in crate::solver) const LADDER_COLLAPSE_MIN_WIDTH: usize = 3;
/// Total derived-binary budget across all ladders of one formula. At the
/// width cap a single ladder derives 8128 binaries; this admits ~123 such
/// ladders (or ~22000 adv_gc-sized ones) while bounding pathological inputs.
pub(in crate::solver) const LADDER_COLLAPSE_MAX_TOTAL_BINARIES: usize = 1_000_000;

/// One recognized sequential-AMO ladder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::solver) struct Ladder {
    /// Base variables in chain order `x_{σ(1)}..x_{σ(k)}`.
    pub(in crate::solver) base: Vec<Variable>,
    /// Register variables in chain order `s_1..s_{k-1}`.
    pub(in crate::solver) aux: Vec<Variable>,
    /// Caller-supplied ids (arena indices) of the ladder's `3k-4` clauses.
    pub(in crate::solver) clause_ids: Vec<usize>,
}

/// Result of one recognition pass.
#[derive(Debug, Default)]
pub(in crate::solver) struct LadderScan {
    pub(in crate::solver) ladders: Vec<Ladder>,
    /// All-negative binaries already present, as `(min, max)` variable-index
    /// pairs — used to avoid re-adding a derived binary the formula has.
    pub(in crate::solver) existing_amo: BTreeSet<(u32, u32)>,
}

/// Streaming scan input. The solver feeds arena clauses without cloning the
/// long ones; only clean binary clauses are retained. Everything else merely
/// disqualifies its variables from serving as ladder registers, which is the
/// cheap gate: a formula without the binary shapes never allocates more than
/// the three per-variable arrays.
pub(in crate::solver) struct LadderScanInput {
    num_vars: usize,
    /// `(caller id, lit0, lit1)` for binary clauses with two distinct,
    /// root-unassigned variables.
    binaries: Vec<(usize, Literal, Literal)>,
    /// Variable may not serve as a ladder register: it occurs in a non-binary
    /// clause, a clause touching a root assignment, or is itself assigned.
    bad: Vec<bool>,
    /// Positive/negative occurrence counts over the clean binaries, saturating
    /// (the candidate filter only needs "≤ 2").
    pos_cnt: Vec<u8>,
    neg_cnt: Vec<u8>,
    existing_amo: BTreeSet<(u32, u32)>,
}

impl LadderScanInput {
    pub(in crate::solver) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            binaries: Vec::new(),
            bad: vec![false; num_vars],
            pos_cnt: vec![0; num_vars],
            neg_cnt: vec![0; num_vars],
            existing_amo: BTreeSet::new(),
        }
    }

    /// Feed one active irredundant clause. `any_assigned` is whether any of
    /// its literals is root-assigned (satisfied OR falsified — a reduced
    /// clause is not the syntactic shape the recognizer certifies).
    pub(in crate::solver) fn add_clause(
        &mut self,
        id: usize,
        lits: &[Literal],
        any_assigned: bool,
    ) {
        let clean_binary = lits.len() == 2
            && !any_assigned
            && lits[0].variable() != lits[1].variable()
            && lits.iter().all(|l| l.variable().index() < self.num_vars);
        if !clean_binary {
            for l in lits {
                let vi = l.variable().index();
                if vi < self.num_vars {
                    self.bad[vi] = true;
                }
            }
            return;
        }
        for l in lits {
            let vi = l.variable().index();
            if l.is_positive() {
                self.pos_cnt[vi] = self.pos_cnt[vi].saturating_add(1);
            } else {
                self.neg_cnt[vi] = self.neg_cnt[vi].saturating_add(1);
            }
        }
        if !lits[0].is_positive() && !lits[1].is_positive() {
            let a = lits[0].variable().0;
            let b = lits[1].variable().0;
            self.existing_amo.insert((a.min(b), a.max(b)));
        }
        self.binaries.push((id, lits[0], lits[1]));
    }

    /// Whether the formula can contain any ladder at all — the O(1) bail-out.
    fn worth_scanning(&self) -> bool {
        !self.binaries.is_empty()
    }
}

/// Per-candidate occurrence classification over the clean binaries.
#[derive(Default)]
struct CandOcc {
    /// `(clause id, other var)` for `(¬other ∨ self)` — the shapes
    /// `(¬x_{σ(i)} ∨ s_i)` and `(¬s_{i-1} ∨ s_i)`.
    pos_in: Vec<(usize, u32)>,
    /// `(clause id, other var)` for `(¬self ∨ other)` — the chain link
    /// `(¬s_i ∨ s_{i+1})`.
    next: Vec<(usize, u32)>,
    /// `(clause id, other var)` for `(¬self ∨ ¬other)` — the AMO step
    /// `(¬x_{σ(i+1)} ∨ ¬s_i)`.
    amo: Vec<(usize, u32)>,
    /// A positive-positive occurrence was seen — never a ladder register.
    disqualified: bool,
}

/// Recognize every strict sequential-AMO ladder in the scanned formula.
pub(in crate::solver) fn detect_ladders(input: &LadderScanInput) -> LadderScan {
    let mut scan = LadderScan {
        ladders: Vec::new(),
        existing_amo: input.existing_amo.clone(),
    };
    if !input.worth_scanning() {
        return scan;
    }

    // Candidate registers: unassigned-clean variables whose binary occurrence
    // counts fit one of the three ladder roles (head 1/2, middle 2/2, tail
    // 2/1). Everything else is settled without occurrence lists.
    let is_candidate = |vi: usize| -> bool {
        if input.bad[vi] {
            return false;
        }
        let (p, n) = (input.pos_cnt[vi], input.neg_cnt[vi]);
        matches!((p, n), (1, 2) | (2, 2) | (2, 1))
    };

    // Occurrence lists only for the candidates (BTreeMap for determinism).
    let mut cand: BTreeMap<u32, CandOcc> = BTreeMap::new();
    for &(id, l0, l1) in &input.binaries {
        for (me, other) in [(l0, l1), (l1, l0)] {
            let vi = me.variable().index();
            if !is_candidate(vi) {
                continue;
            }
            let occ = cand.entry(me.variable().0).or_default();
            match (me.is_positive(), other.is_positive()) {
                (true, false) => occ.pos_in.push((id, other.variable().0)),
                (false, true) => occ.next.push((id, other.variable().0)),
                (false, false) => occ.amo.push((id, other.variable().0)),
                (true, true) => occ.disqualified = true,
            }
        }
    }
    // Shape filter: every occurrence classified, counts per role exact.
    cand.retain(|_, occ| {
        !occ.disqualified
            && occ.amo.len() == 1
            && occ.next.len() <= 1
            && (occ.pos_in.len() == 1 || occ.pos_in.len() == 2)
    });

    // Chain walk from every head (exactly one pos_in — the `(¬x_{σ(1)} ∨ s_1)`
    // clause — plus a live chain link).
    let heads: Vec<u32> = cand
        .iter()
        .filter(|(_, occ)| occ.pos_in.len() == 1 && occ.next.len() == 1)
        .map(|(&v, _)| v)
        .collect();
    let mut recognized: Vec<Ladder> = Vec::new();
    'heads: for head in heads {
        let head_occ = &cand[&head];
        let mut base: Vec<u32> = vec![head_occ.pos_in[0].1];
        let mut aux: Vec<u32> = vec![head];
        let mut clause_ids: Vec<usize> = vec![head_occ.pos_in[0].0];
        let mut cur = head;
        loop {
            if aux.len() > LADDER_COLLAPSE_MAX_WIDTH {
                continue 'heads; // over-width (also breaks any cycle)
            }
            let occ = &cand[&cur];
            let (amo_id, amo_partner) = occ.amo[0];
            if let Some(&(link_id, next_var)) = occ.next.first() {
                // Middle step: the link target must itself be a verified
                // candidate whose SECOND pos_in names the same base variable
                // as this step's AMO partner (the σ-pairing).
                let Some(next_occ) = cand.get(&next_var) else {
                    continue 'heads;
                };
                if next_occ.pos_in.len() != 2 || aux.contains(&next_var) {
                    continue 'heads;
                }
                let mut x_next: Option<(usize, u32)> = None;
                let mut link_seen = 0usize;
                for &(pid, other) in &next_occ.pos_in {
                    if pid == link_id {
                        link_seen += 1;
                        debug_assert_eq!(other, cur);
                    } else {
                        x_next = Some((pid, other));
                    }
                }
                let (Some((x_id, x_var)), 1) = (x_next, link_seen) else {
                    continue 'heads;
                };
                if x_var != amo_partner {
                    continue 'heads; // σ-pairing violated: closure not implied
                }
                clause_ids.extend([link_id, x_id, amo_id]);
                base.push(x_var);
                aux.push(next_var);
                cur = next_var;
            } else {
                // Tail step: the single AMO occurrence names x_{σ(k)}.
                clause_ids.push(amo_id);
                base.push(amo_partner);
                break;
            }
        }
        let k = base.len();
        if !(LADDER_COLLAPSE_MIN_WIDTH..=LADDER_COLLAPSE_MAX_WIDTH).contains(&k) {
            continue;
        }
        debug_assert_eq!(aux.len(), k - 1);
        let base_set: BTreeSet<u32> = base.iter().copied().collect();
        let aux_set: BTreeSet<u32> = aux.iter().copied().collect();
        let id_set: BTreeSet<usize> = clause_ids.iter().copied().collect();
        if base_set.len() != k
            || !base_set.is_disjoint(&aux_set)
            || id_set.len() != 3 * k - 4
            || clause_ids.len() != 3 * k - 4
        {
            continue;
        }
        recognized.push(Ladder {
            base: base.into_iter().map(Variable).collect(),
            aux: aux.into_iter().map(Variable).collect(),
            clause_ids,
        });
    }

    // Cross-ladder strictness: a base variable that is any recognized
    // ladder's register would have its occurrence census invalidated by the
    // other ladder's collapse, so such ladders are dropped wholesale; clause
    // and register claims must be unique.
    let all_aux: BTreeSet<u32> = recognized
        .iter()
        .flat_map(|l| l.aux.iter().map(|v| v.0))
        .collect();
    let mut claimed_clauses: BTreeSet<usize> = BTreeSet::new();
    let mut claimed_aux: BTreeSet<u32> = BTreeSet::new();
    for ladder in recognized {
        if ladder.base.iter().any(|v| all_aux.contains(&v.0)) {
            continue;
        }
        if ladder.aux.iter().any(|v| claimed_aux.contains(&v.0))
            || ladder
                .clause_ids
                .iter()
                .any(|id| claimed_clauses.contains(id))
        {
            continue;
        }
        claimed_aux.extend(ladder.aux.iter().map(|v| v.0));
        claimed_clauses.extend(ladder.clause_ids.iter().copied());
        scan.ladders.push(ladder);
    }
    scan
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

    fn scan(num_vars: usize, clauses: &[Vec<Literal>]) -> LadderScan {
        let mut input = LadderScanInput::new(num_vars);
        for (id, c) in clauses.iter().enumerate() {
            input.add_clause(id, c, false);
        }
        detect_ladders(&input)
    }

    /// A k-wide ladder over base vars `xs` (in σ order) and registers `ss`.
    fn ladder_clauses(xs: &[i32], ss: &[i32]) -> Vec<Vec<Literal>> {
        let k = xs.len();
        assert_eq!(ss.len(), k - 1);
        let mut out = vec![vec![lit(-xs[0]), lit(ss[0])]];
        for i in 1..k - 1 {
            out.push(vec![lit(-xs[i]), lit(ss[i])]);
            out.push(vec![lit(-ss[i - 1]), lit(ss[i])]);
            out.push(vec![lit(-xs[i]), lit(-ss[i - 1])]);
        }
        out.push(vec![lit(-xs[k - 1]), lit(-ss[k - 2])]);
        out
    }

    #[test]
    fn recognizes_a_shuffled_ladder_and_recovers_sigma() {
        // σ = [3, 1, 4, 2] over base vars 1..4, registers 5..7, plus an ALO
        // clause over the base vars (long clauses never touch registers).
        let mut clauses = ladder_clauses(&[3, 1, 4, 2], &[5, 6, 7]);
        clauses.push(vec![lit(1), lit(2), lit(3), lit(4)]);
        let scan = scan(8, &clauses);
        assert_eq!(scan.ladders.len(), 1);
        let l = &scan.ladders[0];
        assert_eq!(
            l.base,
            [3u32, 1, 4, 2].map(Variable::new).to_vec(),
            "base order must be the shuffled σ, not variable order"
        );
        assert_eq!(l.aux, [5u32, 6, 7].map(Variable::new).to_vec());
        assert_eq!(l.clause_ids.len(), 3 * 4 - 4);
    }

    #[test]
    fn rejects_a_register_with_an_outside_occurrence() {
        // Register 5 also occurs in an unrelated binary: the occurrence
        // census fails and NOTHING may collapse — deleting the ladder would
        // leave that outside clause constraining a variable reconstruction
        // then overwrites.
        let mut clauses = ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]);
        clauses.push(vec![lit(-5), lit(8)]);
        assert_eq!(scan(9, &clauses).ladders.len(), 0);

        // Same with a positive occurrence in a long clause.
        let mut clauses = ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]);
        clauses.push(vec![lit(5), lit(8), lit(9)]);
        assert_eq!(scan(10, &clauses).ladders.len(), 0);
    }

    #[test]
    fn rejects_an_incomplete_chain() {
        // Drop the tail AMO clause (¬x4 ∨ ¬s3): s3 loses its AMO occurrence,
        // the walk cannot terminate, and the whole ladder is rejected.
        let mut clauses = ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]);
        let tail = clauses.pop();
        assert_eq!(tail.as_deref(), Some(&[lit(-4), lit(-7)][..]));
        assert_eq!(scan(8, &clauses).ladders.len(), 0);

        // Drop a middle AMO step (¬x2 ∨ ¬s1): the head's shape breaks and no
        // chain starts.
        let mut clauses = ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]);
        let pos = clauses
            .iter()
            .position(|c| c.as_slice() == [lit(-2), lit(-5)])
            .expect("middle AMO step present");
        clauses.remove(pos);
        assert_eq!(scan(8, &clauses).ladders.len(), 0);
    }

    #[test]
    fn rejects_a_sigma_pairing_mismatch() {
        // Rewire step 2's AMO partner from x2 to x3: the pairwise closure is
        // no longer implied (x1 and x2 can both be true), so the recognizer
        // must refuse — this is the strictness that keeps the derived
        // binaries RUP.
        let mut clauses = ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]);
        let pos = clauses
            .iter()
            .position(|c| c.as_slice() == [lit(-2), lit(-5)])
            .expect("middle AMO step present");
        clauses[pos] = vec![lit(-3), lit(-5)];
        assert_eq!(scan(8, &clauses).ladders.len(), 0);
    }

    #[test]
    fn ignores_ladder_free_formulas() {
        // Plain pairwise AMO + ALO: no register shape anywhere.
        let clauses = vec![
            vec![lit(1), lit(2), lit(3)],
            vec![lit(-1), lit(-2)],
            vec![lit(-1), lit(-3)],
            vec![lit(-2), lit(-3)],
        ];
        let scan = scan(4, &clauses);
        assert_eq!(scan.ladders.len(), 0);
        assert_eq!(scan.existing_amo.len(), 3);
    }

    #[test]
    fn rejects_root_assigned_ladders() {
        let mut input = LadderScanInput::new(8);
        for (id, c) in ladder_clauses(&[1, 2, 3, 4], &[5, 6, 7]).iter().enumerate() {
            // Pretend every clause touches a root assignment.
            input.add_clause(id, c, true);
        }
        assert_eq!(detect_ladders(&input).ladders.len(), 0);
    }
}
