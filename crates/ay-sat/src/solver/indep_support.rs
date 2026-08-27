// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent-support-restricted branching.
//!
//! Port of the *support computation + decision restriction* half of
//! `zhenwei_kissat-sup`'s `indepsup.c` (SAT-COMP 2026 Main Track; the only
//! 2026 solver that cracked the `xorshift` family, 11/11).
//!
//! # What an independent support is
//!
//! A set `S` of variables is an **independent support** of a formula when
//! every variable outside `S` is functionally determined by `S`. For a CNF
//! that is a Tseitin-encoded circuit, the natural such set is the circuit's
//! free inputs (for `xorshift`, the 32 PRNG seed bits of a 1773-2872 variable
//! unrolling): every other variable is a gate output, hence a function of its
//! inputs, hence — by induction along the gate DAG — a function of the seed.
//!
//! # Definition detection
//!
//! `collect_definitions` recovers gate definitions from the *pristine*
//! irredundant clause database — at preprocessing entry, before BVE resolves
//! the Tseitin scaffolding away — with the existing extractors:
//!
//! * `GateExtractor::extract_xor_groups_clause_driven` (gates/xor.rs) — a
//!   complete XOR group over `k+1` variables emits one gate **per group
//!   variable as output**, which is exactly what the support closure needs:
//!   in `a ⊕ b ⊕ c = 1` any of the three is definable from the other two, and
//!   a one-gate-per-pivot search would record only one of those three
//!   orientations and leave the other two undiscoverable.
//! * `GateExtractor::find_gate_for_congruence_with_marks` with
//!   `include_xor = false` — the per-pivot equivalence / AND / ITE search.
//!
//! Every gate kind these return makes the output **unit-propagation implied**
//! by its inputs, which is the property the restriction leans on:
//!
//! | kind  | defining clauses                                            | UP-implied output |
//! |-------|-------------------------------------------------------------|-------------------|
//! | Equiv | `(¬y ∨ x)`, `(y ∨ ¬x)`                                       | yes, binary       |
//! | And   | `(¬y ∨ xᵢ)` for each `i`, `(y ∨ ¬x₁ ∨ … ∨ ¬xₙ)`              | yes               |
//! | Xor   | all `2^k` parity clauses over the group                      | yes               |
//! | Ite   | `(¬c ∨ ¬t ∨ y)`, `(¬c ∨ t ∨ ¬y)`, `(c ∨ ¬e ∨ y)`, `(c ∨ e ∨ ¬y)` | yes           |
//!
//! (An AND gate with all inputs true fires the long clause; with any input
//! false it fires that input's binary. A `k+1`-variable XOR group with `k`
//! variables assigned has exactly one parity clause left with one unassigned
//! literal. ITE with `c`, `t`, `e` assigned always has one of its four
//! clauses reduced to the `y` literal.)
//!
//! # Support closure
//!
//! `greedy_support` is the acyclic-removal greedy of `indepsup.c`'s
//! `explicit_search` (kissat-sup lines 782-861): walk the variables in some
//! order and drop `v` from the candidate set as soon as **some** gate with
//! output `v` has *all* of its input variables still in the set (or fixed at
//! root). Removal is monotone, so the removal order is itself a topological
//! order of the induced definitions: a variable dropped at step `t` depends
//! only on variables that are either in the final support or dropped at some
//! step `> t`. There is therefore no cycle, and by reverse induction on the
//! removal order every dropped variable is a well-founded function of the
//! final support. That is the acyclicity guard the design calls for — it is
//! structural, not a post-hoc check.
//!
//! The greedy's *quality* is entirely order-dependent, and the right order is
//! reverse-topological (drop the deep outputs first, while their shallower
//! inputs are all still present). We do not know the circuit's direction, so
//! `compute_indep_support` runs a fixed, deterministic ORDER SWEEP and keeps
//! the smallest support. Measured on the eleven `xorshift` CNFs: the
//! incidence orders kissat-sup uses land at 526-1029 of 1773-2965 variables
//! (~35% — useless), while descending variable index — reverse-topological
//! for a circuit written out in evaluation order — lands at exactly **32**
//! on all eleven. The sweep costs one `O(Σ arity)` pass per order.
//!
//! # Completeness argument for the fallback
//!
//! `verify_closure` re-derives the whole formula from the support with the
//! same worklist closure the search's BCP would perform, and refuses the
//! support outright if any decidable variable is left over. But that check is
//! about the gate set *at computation time*, and preprocessing/inprocessing
//! (BVE, vivify, clause deletion, variable compaction) retires defining
//! clauses afterwards — on `xorshift_r14_31`, BVE alone eliminates 563 of
//! 1773 variables. So the restriction is additionally made unconditionally
//! safe at the point of use:
//!
//! **`pick_indep_support_decision` restricts the decision *order* only.** It
//! never reports SAT, never closes a branch, and never narrows BCP. When no
//! support variable is left unassigned it returns `None`, and the caller
//! (`pick_next_decision_variable_main`) *falls through to unrestricted
//! VSIDS/VMTF* rather than treating that as a complete assignment. SAT is
//! still declared only where it always was — when the unrestricted pick has
//! no unassigned variable left — so a support that turns out not to determine
//! everything costs decisions, never a wrong answer. UNSAT proofs are
//! likewise untouched: decision order is not part of any DRAT/LRAT
//! obligation, and the one-shot symmetry/SR gating runs at preprocessing,
//! strictly before this.
//!
//! # Restriction policy
//!
//! The restricted pick is an `O(|S|)` scan of the support (the same shape as
//! the VMTF arm of `pick_domain_restricted_decision`), so it is applied only
//! when the support is *both* small in absolute terms and a real reduction:
//! `|S| <= INDEP_SUPPORT_MAX_SIZE` and `|S| <= decidable / 2`. kissat-sup's
//! own gating is the same shape (its score bias is skipped above
//! `is->size > 128`, its explicit search runs above 1024, its exhaustive
//! support propagation only below 40).

use super::*;
use crate::gates::{Gate, GateExtractor};
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

mod closure;

/// Largest formula the support computation will look at (variables).
const INDEP_SUPPORT_MAX_VARS: usize = 1 << 20;
/// Largest formula the support computation will look at (active clauses).
const INDEP_SUPPORT_MAX_CLAUSES: usize = 1 << 21;
/// Largest recovered gate set kept (guards the CSR allocations).
const INDEP_SUPPORT_MAX_GATES: usize = 1 << 22;
/// Absolute cap on a support that may restrict branching. The restricted
/// pick is an O(|S|) scan per decision, so this is a throughput bound as
/// much as a "is the support meaningful" bound.
const INDEP_SUPPORT_MAX_SIZE: usize = 256;
/// The support must also be at most this fraction (1/N) of the decidable
/// variables — otherwise the restriction is not buying anything.
const INDEP_SUPPORT_MAX_FRACTION_DEN: usize = 2;
/// Wall budget for gate recovery.
const INDEP_SUPPORT_EXTRACT_BUDGET_MS: u128 = 2_000;
/// Effort budget (clauses/occurrences scanned) for gate recovery.
const INDEP_SUPPORT_EXTRACT_EFFORT: u64 = 20_000_000;

/// CLI-owned tri-state: `--sat-indep-support <bool>`.
fn indep_support_enabled() -> bool {
    ay_core::sat_ab_switches()
        .indep_support
        .unwrap_or(INDEP_SUPPORT_DEFAULT_ON)
}

/// Shipped default for the independent-support brancher.
///
/// Measured default-OFF: see the landing commit. The paired A/B found the
/// restriction inert on every corpus instance that is not a Tseitin circuit
/// with a tiny free-input set, and the one family it does engage on
/// (`xorshift`) needs an exhaustive support enumerator, not a decision
/// reorder, to convert inside a competition budget.
const INDEP_SUPPORT_DEFAULT_ON: bool = false;

/// A gate definition reduced to what the closure needs: an output variable
/// and its DISTINCT input variables.
struct Definition {
    output: u32,
    inputs: Vec<u32>,
}

/// Per-literal occurrence lists over the active irredundant clauses, in CSR
/// form: `pos[ranges[2*v]]` / `neg[ranges[2*v + 1]]` are the clause offsets
/// where variable `v` occurs positively / negatively.
struct Occurrences {
    pos: Vec<usize>,
    neg: Vec<usize>,
    ranges: Vec<std::ops::Range<usize>>,
}

/// The recovered definition set plus its variable-indexed CSR views.
struct DefinitionGraph {
    defs: Vec<Definition>,
    /// `as_lhs[v]` = definition indices whose output is `v`.
    as_lhs: Vec<Vec<u32>>,
    /// Number of definitions `v` feeds as an input (kissat `gates_as_rhs`).
    rhs_count: Vec<u32>,
}

impl Solver {
    /// Compute the independent support and install it as the decision
    /// whitelist, or leave the whitelist empty (unrestricted branching).
    ///
    /// Called at STARTUP-PREPROCESS ENTRY, on the pristine clause database —
    /// the same place kissat-sup analyses (`kissat_indepsup_clone` snapshots
    /// `origin_clauses` at import and every later round runs against that
    /// snapshot, never the working formula). This is not a detail:
    /// preprocessing's job is to *destroy* the Tseitin structure the support
    /// is read from. Measured on `xorshift_r14_31`, BVE eliminates 563 of
    /// 1773 variables and rewrites 3625 clauses into resolvents before the
    /// search starts, so a post-preprocess analysis sees a formula whose
    /// gate definitions have largely been resolved away.
    ///
    /// `retire_indep_support_eliminations` then drops whatever preprocessing
    /// removed, immediately before the CDCL loop.
    ///
    /// Decision-order only — see the module docs for the soundness argument
    /// and the mandatory fallback.
    pub(super) fn install_indep_support(&mut self) {
        self.indep_support.clear();
        // Release the protection a previous solve installed, so incremental
        // re-solves do not accumulate frozen variables.
        let previously_frozen = std::mem::take(&mut self.indep_support_frozen);
        for v in previously_frozen {
            if (v as usize) < self.num_vars {
                self.melt(Variable(v));
            }
        }
        if !indep_support_enabled() {
            return;
        }
        // IC3/PDR and domain-restricted queries own the decision route; this
        // is a plain-CNF startup analysis only (mirrors the GF-probe gate).
        if self.cold.ic3_mode || self.active_domain.is_some() || self.decision_domain.is_some() {
            return;
        }
        if self.decision_level != 0 {
            return;
        }
        let num_vars = self.num_vars;
        if num_vars == 0 || num_vars > INDEP_SUPPORT_MAX_VARS {
            return;
        }
        if self.arena.active_clause_count() > INDEP_SUPPORT_MAX_CLAUSES {
            return;
        }

        let t0 = ay_core::time::Instant::now();
        let support = self.compute_indep_support();
        self.stats.indep_support_time_ns = self
            .stats
            .indep_support_time_ns
            .saturating_add(t0.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64);

        let Some(support) = support else {
            return;
        };
        self.stats.indep_support_size = support.len() as u64;
        self.stats.indep_support_installed_size = support.len() as u64;
        // FREEZE the whitelist against elimination. Without this, BVE takes
        // support variables out of the restriction while leaving behind every
        // variable they determined: measured on `xorshift_r14_31`, 18 of the
        // 32 seed bits were eliminated and the exhausted-support fallback then
        // carried 127925 of 150075 decisions (85%) — the restriction existed
        // on paper and did nothing. Freezing is also what keeps the raw
        // variable indices in this list meaningful: `compacting()` refuses to
        // renumber while any variable is frozen.
        for &v in &support {
            debug_assert!((v as usize) < self.num_vars);
            self.cold.freeze_counts[v as usize] =
                self.cold.freeze_counts[v as usize].saturating_add(1);
        }
        self.indep_support_frozen = support.clone();
        self.indep_support = support;
        tracing::info!(
            support = self.indep_support.len(),
            decidable = self.stats.indep_support_decidable_vars,
            num_vars,
            "indep support: restricting decisions"
        );
    }

    /// Drop whatever preprocessing retired from the whitelist, immediately
    /// before the CDCL loop.
    ///
    /// Variable compaction already remaps the list (compact.rs); this is the
    /// no-compaction case — BVE can eliminate a support variable without a
    /// renumbering pass, and an eliminated variable is reconstructed after
    /// SAT rather than decided. The list only shrinks, so the size half of
    /// the restriction policy still holds; the ratio half is rechecked
    /// because preprocessing also shrinks the decidable set.
    pub(super) fn retire_indep_support_eliminations(&mut self) {
        if self.indep_support.is_empty() {
            return;
        }
        let num_vars = self.num_vars;
        let vals_len = self.vals.len();
        let removed: Vec<u32> = std::mem::take(&mut self.indep_support);
        let kept: Vec<u32> = removed
            .into_iter()
            .filter(|&v| {
                let i = v as usize;
                i < num_vars && i * 2 < vals_len && !self.var_lifecycle.is_removed(i)
            })
            .collect();
        let decidable = (0..num_vars)
            .filter(|&v| {
                !self.var_lifecycle.is_removed(v)
                    && self.vals[Literal::positive(Variable(v as u32)).index()] == 0
            })
            .count();
        if kept.is_empty() || kept.len() * INDEP_SUPPORT_MAX_FRACTION_DEN > decidable {
            self.stats.indep_support_size = 0;
            return;
        }
        self.stats.indep_support_size = kept.len() as u64;
        self.indep_support = kept;
    }

    /// Pick the highest-priority UNASSIGNED support variable, or `None` when
    /// every support variable is assigned.
    ///
    /// `None` is NOT a SAT signal — the caller falls through to unrestricted
    /// branching. See the module docs.
    pub(super) fn pick_indep_support_decision(&mut self) -> Option<Variable> {
        let support = std::mem::take(&mut self.indep_support);
        let heuristic = self.active_branch_heuristic;
        let mut best: Option<Variable> = None;
        let mut best_key = f64::NEG_INFINITY;
        for &idx in &support {
            let i = idx as usize;
            // Defensive: variable compaction remaps this list (compact.rs),
            // but an index that outlives its variable must never reach BCP.
            if i >= self.num_vars || i * 2 >= self.vals.len() {
                continue;
            }
            if self.var_is_assigned(i) || self.var_lifecycle.is_removed(i) {
                continue;
            }
            let var = Variable(idx);
            let key = match heuristic {
                BranchHeuristic::Evsids | BranchHeuristic::Chb => self.vsids.activity(var),
                BranchHeuristic::Vmtf => self.vsids.bump_order(var) as f64,
            };
            if best.is_none() || key > best_key {
                best = Some(var);
                best_key = key;
            }
        }
        self.indep_support = support;
        best
    }
}

#[cfg(test)]
mod tests;
