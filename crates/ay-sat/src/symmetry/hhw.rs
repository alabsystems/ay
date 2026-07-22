// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Heule-Hunt-Wetzler (CADE 2015, "Expressing Symmetry Breaking in DRAT
//! Proofs") symmetry → DRAT construction — the leading-lex-clause ("lead")
//! variant, a faithful port of `tools/hhw-symmetry-drat/hhw.py`.
//!
//! For a sign-preserving variable automorphism σ of a CNF F, [`build_lead`]
//! emits a partial DRAT proof fragment (plain RUP/RAT additions + deletions)
//! over the ORIGINAL clauses, plus the leading lex-leader symmetry clause. The
//! three steps (HHW §5) are:
//!
//!  1. **Definitions** (RAT/blocked on the fresh blocking literal): the swap
//!     gadget `s_i` with `s_1 ↔ [x >_lex σ·x]` (`6n−3` clauses, emitted
//!     high→low index so each is blocked on its fresh `s`-literal), then the
//!     renamed-variable defs `x'_i ↔ (s_1 ? σ(x_i) : x_i)` (`4n` clauses).
//!  2. **Redefine involved clauses** `C_j → C'_j` (support renamed to `x'`).
//!     `C'_j ∪ {s_1}` is RUP via the σ-IMAGE `σ(C_j) ∈ F` (image-and-chain);
//!     `C'_j` is RUP via `C_j` + that scaffold. The scaffolds are added while
//!     every original AND its σ-image is intact, THEN deleted (two-phase).
//!  3. **Leading SBP** over `x'`: the leading lex clause `(¬x'_1 ∨ p'_1)` via an
//!     `s_1` case-split (`L∨s_1` and `L∨¬s_1` are each RUP via the gadget, then
//!     `L` by resolution; the two scaffolds are deleted).
//!
//! ## Integration note: originals are RETAINED
//!
//! The Python prototype RETIRES the original involved clauses `C_j` (deletes
//! them in phase B) so the residual solve runs on `F'` alone. This Rust port,
//! wired into AY's live `--proof drat` emit path, KEEPS the originals: it emits
//! every step above EXCEPT the original-clause deletions, and adds the surviving
//! new clauses ([`HhwStep::AddKeep`]) to the solver DB. Retaining the originals
//! keeps the solver's clause DB identical to the proof's active set WITHOUT
//! root-clause arena surgery, is satisfiability-preserving (the kept clauses are
//! a superset), and STILL natively verifies the full image-and-chain + leading
//! SBP against the original CNF — every emitted addition is RUP/RAT-valid at the
//! moment it is added (deletions only ever make later RUP checks easier). The
//! leading SBP clause still prunes the residual search through the iff-gadget
//! that ties `x'` to `x`. Retiring the originals (solving `F'`) is the only HHW
//! step this port omits; see the report for the honest boundary.

use std::collections::{BTreeMap, BTreeSet};

use crate::{Literal, Variable};

/// One step of the emitted partial DRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HhwStep {
    /// A clause that SURVIVES into `F'` (a gadget def, an `x'`-def, a renamed
    /// involved clause `C'_j`, or the leading SBP clause): emit it as a plain
    /// DRAT `a`-line AND add it to the solver clause DB.
    AddKeep(Vec<Literal>),
    /// A transient scaffold (`C'_j ∪ {s_1}` or `L ∪ {±s_1}`): emit it as a plain
    /// DRAT `a`-line for the proof only; it is deleted again before `F'` and
    /// never enters the solver clause DB.
    AddScaffold(Vec<Literal>),
    /// Delete a (scaffold) clause from the proof's active set (DRAT `d`-line).
    Delete(Vec<Literal>),
}

/// The result of building the HHW leading-clause fragment for one automorphism.
#[derive(Debug, Clone)]
pub(crate) struct HhwLead {
    /// Ordered partial-proof steps. The ORDER is load-bearing: the RAT/blocked
    /// gadget clauses are emitted high→low index, and each scaffold is added
    /// while its σ-image is still present.
    pub(crate) steps: Vec<HhwStep>,
    /// The leading lex-leader clause `(¬x'_1 ∨ p'_1)` over the renamed vars (this
    /// is also present as the final [`HhwStep::AddKeep`] step; surfaced for
    /// tests/logging).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) leading_clause: Vec<Literal>,
    /// Total variable COUNT after the fresh `s_i` / `x'_i` allocation. The caller
    /// must `ensure_num_vars(new_var_count)` before applying the steps.
    pub(crate) new_var_count: u32,
}

/// Build the HHW leading-lex-clause DRAT fragment for the sign-preserving
/// automorphism `sigma` (a `var → var` map; its keys are the moved support, a
/// permutation of themselves). `fresh_base` is the first unused variable index
/// (= the current `num_vars`); the fresh `s_i` and `x'_i` are allocated from
/// there. Returns `None` if `sigma` is not a fixed-point-free closed permutation
/// of its support (emitting nothing is always sound).
pub(crate) fn build_lead(
    clauses: &[Vec<Literal>],
    sigma: &BTreeMap<Variable, Variable>,
    fresh_base: u32,
) -> Option<HhwLead> {
    // Support in ascending variable-id order (BTreeMap keys are sorted).
    let support: Vec<Variable> = sigma.keys().copied().collect();
    let n = support.len();
    if n == 0 {
        return None;
    }
    // σ must be a fixed-point-free permutation of its OWN support: build the
    // inverse and require image-set == support. Emitting no constraint is always
    // sound, so reject (rather than risk a degenerate gadget) on any violation.
    let mut inv: BTreeMap<Variable, Variable> = BTreeMap::new();
    for (k, v) in sigma {
        if k == v {
            return None; // fixed point listed in the support: degenerate gadget
        }
        inv.insert(*v, *k);
    }
    if inv.len() != sigma.len() {
        return None; // not injective
    }
    if !support.iter().all(|v| inv.contains_key(v)) {
        return None; // image set differs from the support
    }

    // 1-based position of each support variable.
    let pos: BTreeMap<Variable, usize> = support
        .iter()
        .enumerate()
        .map(|(i, v)| (*v, i + 1))
        .collect();

    // Fresh allocation (0-indexed): s_i = fresh_base+(i-1); x'_i = fresh_base+n+(i-1).
    let n_u32 = n as u32;
    let s_var = |i: usize| Variable::new(fresh_base + (i as u32 - 1));
    let xp_var = |i: usize| Variable::new(fresh_base + n_u32 + (i as u32 - 1));
    let new_var_count = fresh_base + 2 * n_u32;

    // σ(x_i) as a variable (sign-preserving ⇒ the positive literal of this var).
    let img = |i: usize| *sigma.get(&support[i - 1]).expect("support key present");
    // p'_i = x'_{pos[σ(x_i)]} (renamed image of position i).
    let ppi = |i: usize| xp_var(*pos.get(&img(i)).expect("σ(x_i) lies in the support"));

    let lp = Literal::positive;
    let ln = Literal::negative;

    let mut steps: Vec<HhwStep> = Vec::new();

    // --- STEP 1a: swap gadget (blocked, high index → low) ---------------------
    for i in (1..=n).rev() {
        let xi = support[i - 1];
        let pi = img(i);
        let si = s_var(i);
        if i < n {
            let sip = s_var(i + 1);
            // s_i clauses (RAT on +s_i), added before the −s_i ones.
            steps.push(HhwStep::AddKeep(vec![lp(si), ln(xi), lp(pi)]));
            steps.push(HhwStep::AddKeep(vec![lp(si), ln(xi), ln(sip)]));
            steps.push(HhwStep::AddKeep(vec![lp(si), lp(pi), ln(sip)]));
            // −s_i clauses (RAT on −s_i).
            steps.push(HhwStep::AddKeep(vec![ln(si), lp(xi), ln(pi)]));
            steps.push(HhwStep::AddKeep(vec![ln(si), lp(xi), lp(sip)]));
            steps.push(HhwStep::AddKeep(vec![ln(si), ln(pi), lp(sip)]));
        } else {
            steps.push(HhwStep::AddKeep(vec![lp(si), ln(xi), lp(pi)]));
            steps.push(HhwStep::AddKeep(vec![ln(si), lp(xi)]));
            steps.push(HhwStep::AddKeep(vec![ln(si), ln(pi)]));
        }
    }

    // --- STEP 1b: renamed-variable definitions (blocked on x'_i) --------------
    let s1 = s_var(1);
    for i in 1..=n {
        let xi = support[i - 1];
        let pi = img(i);
        let xpi = xp_var(i);
        // x'_i positive clauses (RAT on +x'_i).
        steps.push(HhwStep::AddKeep(vec![lp(xpi), ln(xi), lp(s1)]));
        steps.push(HhwStep::AddKeep(vec![lp(xpi), ln(pi), ln(s1)]));
        // x'_i negative clauses (RAT on −x'_i).
        steps.push(HhwStep::AddKeep(vec![ln(xpi), lp(xi), lp(s1)]));
        steps.push(HhwStep::AddKeep(vec![ln(xpi), lp(pi), ln(s1)]));
    }

    // --- STEP 2: redefine involved clauses (image-and-chain) ------------------
    // Two-phase: add every scaffold `C'_j ∪ {s_1}` and `C'_j` while the original
    // `C_j` AND its σ-image are intact, THEN delete the scaffolds. (Originals are
    // retained — see the module docs — so no original-deletion `d`-lines.)
    let supp: BTreeSet<Variable> = support.iter().copied().collect();
    let mut scaffolds: Vec<Vec<Literal>> = Vec::new();
    for cj in clauses {
        if !cj.iter().any(|l| supp.contains(&l.variable())) {
            continue;
        }
        let cp = rename_clause(cj, &pos, fresh_base, n_u32);
        let mut scaffold = cp.clone();
        scaffold.push(lp(s1)); // C'_j ∪ {s_1}
        steps.push(HhwStep::AddScaffold(scaffold.clone()));
        steps.push(HhwStep::AddKeep(cp));
        scaffolds.push(scaffold);
    }
    for scaffold in &scaffolds {
        steps.push(HhwStep::Delete(scaffold.clone()));
    }

    // --- STEP 3: leading lex clause (¬x'_1 ∨ p'_1) via an s_1 case-split -------
    let l1 = vec![ln(xp_var(1)), lp(ppi(1))];
    let mut l1_s = l1.clone();
    l1_s.push(lp(s1));
    let mut l1_ns = l1.clone();
    l1_ns.push(ln(s1));
    steps.push(HhwStep::AddScaffold(l1_s.clone()));
    steps.push(HhwStep::AddScaffold(l1_ns.clone()));
    steps.push(HhwStep::AddKeep(l1.clone()));
    steps.push(HhwStep::Delete(l1_s));
    steps.push(HhwStep::Delete(l1_ns));

    Some(HhwLead {
        steps,
        leading_clause: l1,
        new_var_count,
    })
}

/// Rename a clause's support literals to the corresponding `x'` variables,
/// preserving sign; non-support literals are left untouched.
fn rename_clause(
    clause: &[Literal],
    pos: &BTreeMap<Variable, usize>,
    fresh_base: u32,
    n: u32,
) -> Vec<Literal> {
    clause
        .iter()
        .map(|&l| {
            let v = l.variable();
            if let Some(&p) = pos.get(&v) {
                let xp = Variable::new(fresh_base + n + (p as u32 - 1));
                if l.is_positive() {
                    Literal::positive(xp)
                } else {
                    Literal::negative(xp)
                }
            } else {
                l
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: u32) -> Variable {
        Variable::new(i)
    }

    /// σ = (var0 ↔ var1) over a 2-variable formula; fresh_base = 2.
    fn two_var() -> (Vec<Vec<Literal>>, BTreeMap<Variable, Variable>) {
        let clauses = vec![
            vec![Literal::positive(v(0)), Literal::positive(v(1))],
            vec![Literal::negative(v(0)), Literal::negative(v(1))],
            vec![Literal::negative(v(0)), Literal::positive(v(1))],
            vec![Literal::positive(v(0)), Literal::negative(v(1))],
        ];
        let mut sigma = BTreeMap::new();
        sigma.insert(v(0), v(1));
        sigma.insert(v(1), v(0));
        (clauses, sigma)
    }

    fn count_adds(b: &HhwLead) -> (usize, usize, usize) {
        let mut keep = 0;
        let mut scaffold = 0;
        let mut del = 0;
        for s in &b.steps {
            match s {
                HhwStep::AddKeep(_) => keep += 1,
                HhwStep::AddScaffold(_) => scaffold += 1,
                HhwStep::Delete(_) => del += 1,
            }
        }
        (keep, scaffold, del)
    }

    #[test]
    fn lead_allocates_2n_fresh_vars_and_leading_clause_is_over_xprime() {
        let (clauses, sigma) = two_var();
        let b = build_lead(&clauses, &sigma, 2).expect("builds");
        // n = 2 → s_1=2,s_2=3, x'_1=4,x'_2=5 → new_var_count = 2 + 2*2 = 6.
        assert_eq!(b.new_var_count, 6);
        // Leading clause: (¬x'_1 ∨ p'_1) = (¬var4 ∨ +var5) since σ(x_1)=var1 at pos 2.
        assert_eq!(
            b.leading_clause,
            vec![Literal::negative(v(4)), Literal::positive(v(5))]
        );
    }

    #[test]
    fn lead_emits_6n_minus_3_gadget_plus_4n_defs_plus_renamed_plus_leader() {
        let (clauses, sigma) = two_var();
        let b = build_lead(&clauses, &sigma, 2).expect("builds");
        let (keep, scaffold, del) = count_adds(&b);
        // All 4 clauses are involved (every clause mentions var0 or var1).
        let n = 2;
        let gadget = 6 * n - 3; // 9
        let defs = 4 * n; // 8
        let renamed = 4; // one C'_j per involved clause
        let leader = 1;
        assert_eq!(keep, gadget + defs + renamed + leader);
        // Scaffolds: one per involved clause (C'_j∪{s1}) + 2 for the leader split.
        assert_eq!(scaffold, renamed + 2);
        // Deletions: the scaffolds (originals are retained, so no original d-lines).
        assert_eq!(del, scaffold);
    }

    #[test]
    fn lead_gadget_first_three_clauses_match_high_to_low_order() {
        let (clauses, sigma) = two_var();
        let b = build_lead(&clauses, &sigma, 2).expect("builds");
        // i=n=2 first: xi=var1, pi=σ(var1)=var0, si=s_2=var3.
        //   [+s2,¬x1,+x0], [¬s2,+x1], [¬s2,¬x0]
        let expect = [
            HhwStep::AddKeep(vec![
                Literal::positive(v(3)),
                Literal::negative(v(1)),
                Literal::positive(v(0)),
            ]),
            HhwStep::AddKeep(vec![Literal::negative(v(3)), Literal::positive(v(1))]),
            HhwStep::AddKeep(vec![Literal::negative(v(3)), Literal::negative(v(0))]),
        ];
        assert_eq!(&b.steps[0..3], &expect[..]);
    }

    #[test]
    fn lead_no_clause_has_duplicate_or_complementary_literals() {
        let (clauses, sigma) = two_var();
        let b = build_lead(&clauses, &sigma, 2).expect("builds");
        for s in &b.steps {
            let lits = match s {
                HhwStep::AddKeep(c) | HhwStep::AddScaffold(c) | HhwStep::Delete(c) => c,
            };
            let mut vars: Vec<u32> = lits.iter().map(|l| l.variable().0).collect();
            vars.sort_unstable();
            assert!(
                vars.windows(2).all(|w| w[0] != w[1]),
                "duplicate/complementary variable in emitted clause: {lits:?}"
            );
        }
    }

    #[test]
    fn lead_rejects_fixed_point_and_non_closed_support() {
        // Fixed point listed in support.
        let mut sigma = BTreeMap::new();
        sigma.insert(v(0), v(0));
        assert!(build_lead(&[], &sigma, 1).is_none());
        // Non-closed support: var0→var1 but var1 not a key (image set ≠ support).
        let mut sigma2 = BTreeMap::new();
        sigma2.insert(v(0), v(1));
        assert!(build_lead(&[], &sigma2, 2).is_none());
    }

    #[test]
    fn lead_renames_only_support_literals() {
        // Clause over support var0 and a non-support var7; σ=(var0↔var1).
        let clauses = vec![vec![Literal::positive(v(0)), Literal::negative(v(7))]];
        let mut sigma = BTreeMap::new();
        sigma.insert(v(0), v(1));
        sigma.insert(v(1), v(0));
        let b = build_lead(&clauses, &sigma, 8).expect("builds");
        // fresh_base=8, n=2 → x'_1=10 (8+2+0). The renamed C'_j replaces var0 by
        // x'_1=var10 (pos 1) and keeps var7. Find the AddKeep that is the renamed
        // involved clause (length 2, over var10 and var7).
        let renamed = b.steps.iter().find_map(|s| match s {
            HhwStep::AddKeep(c)
                if c.len() == 2
                    && c.iter().any(|l| l.variable() == v(10))
                    && c.iter().any(|l| l.variable() == v(7)) =>
            {
                Some(c.clone())
            }
            _ => None,
        });
        assert_eq!(
            renamed,
            Some(vec![Literal::positive(v(10)), Literal::negative(v(7))])
        );
    }
}
