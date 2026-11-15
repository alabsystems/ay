// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Justified LRA bounds: the only bounds a LIA VERDICT may rest on
//! (#nia-sign-cut-soundness).
//!
//! ## The invariant
//!
//! The LRA bound store holds two kinds of bound:
//!
//! - **justified** bounds, whose non-sentinel reasons are all currently
//!   asserted atoms (own trail, cross-theory trail, or LIA's own trail), or
//!   whose reasons are sentinel-only (factor-split case hypotheses, Gomory /
//!   HNF cuts, axiom bounds — consequences the enclosing exact procedure owns);
//! - **unjustified** bounds, whose reasons cite something that is NOT an
//!   asserted atom. The NIA's model-derived tentative bounds are exactly
//!   these: `inject_tentative_sign_cuts` (`x >= 0` / `x <= 0` from the CURRENT
//!   model value), `try_integer_rounding` and `try_tentative_patch` pins
//!   (`x = round(model(x))`), and every McCormick row built on such a bound,
//!   all go through `add_gomory_cut(.., reason = <variable or monomial term>)`,
//!   and a term is never an asserted atom. They are heuristics that steer
//!   the LP toward a model the NIA can verify; they are NOT theorems.
//!
//! The simplex conflict path already enforces this distinction: a Farkas
//! conflict citing an unjustified bound is rejected by the #8764 stale-reason
//! guard and the bound is retracted (#A2). What was missing — measured as 18
//! satisfiable QF_NIA problems answered `unsat` on main `b1c1f8f201`, see
//! `benchmarks/smt/wrong-verdict/sat_nia_sign_cut_{1,2,3}.smt2` — is the same
//! discipline in the LIA's own side checks, which read `lra.get_bounds` and
//! return `self.asserted` as the conflict: `check_modular_for_var`, the direct
//! enumeration box, the Diophantine fixed-variable fold, the tableau GCD
//! folds, the Nelson-Oppen tight-bound scans. Each of those laundered a guess
//! into an all-asserted conflict.
//!
//! ## The rule
//!
//! Every LIA site that turns bound VALUES into a verdict, a conflict, a
//! propagated equality, or a derived bound with clean reasons reads bounds
//! through the accessors here, which return an unjustified bound as ABSENT.
//! Reads that only steer (branching split points, model-value heuristics,
//! tightness comparisons) may keep the raw accessors.
//!
//! The second half of the discipline is the exit guard in
//! `theory_impl.rs::check` / `check_during_propagate`: a LIA `Unsat` whose
//! literals are not all live is never published. Together: no LIA verdict
//! can rest on a bound that is not a consequence of the asserted atoms.

use super::*;

impl LiaSolver<'_> {
    /// Whether `bound` is justified by the current assignment: every
    /// non-sentinel reason (direct and provenance) is currently asserted on
    /// the LRA's own trail, its cross-theory trail, or LIA's own trail.
    /// Sentinel-only and axiom bounds are justified (they belong to an
    /// enclosing exact procedure — see the module docs).
    pub fn bound_is_justified(&self, bound: &Bound) -> bool {
        if self.lra.bound_reasons_all_asserted(bound) {
            return true;
        }
        // LRA's trails did not cover every reason. Fall back to LIA's own
        // trail for the literals the LRA never saw (mirrors
        // `conflict_reasons_all_live`). Rare: only shared-equality bounds
        // with LIA-only reasons reach this branch.
        // A term that is not a Boolean atom is never a premise, whichever
        // trail echoes it (see `LraSolver::bound_reasons_all_asserted`).
        let live = |term: TermId, value: bool| -> bool {
            term.is_sentinel()
                || (value && self.is_reasonless_shared_placeholder(term))
                || (*self.terms().sort(term) == Sort::Bool
                    && (self
                        .lra
                        .conflict_literals_all_asserted(&[TheoryLit::new(term, value)])
                        || self.asserted.iter().any(|&(t, v)| t == term && v == value)))
        };
        if !bound.reason_pairs().all(|(t, v)| live(t, v)) {
            return false;
        }
        match bound.provenance.as_ref() {
            Some(provenance) => provenance.reasons_all(&live),
            None => true,
        }
    }

    /// Whether `term` is the placeholder reason `(lhs, true)` of a shared
    /// equality that arrived with NO reason literals (`assert_shared_equality`
    /// installs `lhs = rhs` citing `lhs` itself then), outside any NIA guess
    /// scope (#nonlinear-shared-reasons).
    ///
    /// Main's side checks read those bounds as facts (they read every bound);
    /// the justified-bounds rule rejected them like a guess, since the
    /// placeholder is a term, and that cost plain QF_UFLIA verdicts (measured:
    /// `xs-12-20-1-1-5-2`, `sat` in 2 s on main, `unknown` at 60 s). A
    /// reasonless shared equality is the other theory's unconditional claim;
    /// it is accepted exactly as main accepted it, EXCEPT while an NIA guess
    /// scope is open: a guess on `lhs` cites the same term `(lhs, true)` and
    /// must not be mistaken for the equality.
    fn is_reasonless_shared_placeholder(&self, term: TermId) -> bool {
        !self.in_tentative_scope()
            && self
                .shared_equalities
                .iter()
                .any(|(lhs, _, reasons)| reasons.is_empty() && *lhs == term)
    }

    /// Whether `bound` cites at least one non-sentinel reason atom. A
    /// justified bound with none is a sentinel-only HYPOTHESIS (a factor-split
    /// case pin, the NIA's tentative-patch verification pin): a fact for the
    /// duration of its scope, owned by the procedure that asserted it. State
    /// that is cached ACROSS pops (the Diophantine substitution caches, keyed
    /// on the equality set) must not fold such a bound in.
    pub(crate) fn bound_has_atom_reason(bound: &Bound) -> bool {
        bound.reason_pairs().any(|(t, _)| !t.is_sentinel())
    }

    /// `lra.get_bounds`, with an unjustified side reported as absent.
    pub fn justified_bounds(&self, term: TermId) -> Option<(Option<Bound>, Option<Bound>)> {
        let (lower, upper) = self.lra.get_bounds_ref(term)?;
        Some((
            lower.filter(|b| self.bound_is_justified(b)).cloned(),
            upper.filter(|b| self.bound_is_justified(b)).cloned(),
        ))
    }

    /// `lra.get_bounds_ref`, with an unjustified side reported as absent.
    pub fn justified_bounds_ref(&self, term: TermId) -> Option<(Option<&Bound>, Option<&Bound>)> {
        let (lower, upper) = self.lra.get_bounds_ref(term)?;
        Some((
            lower.filter(|b| self.bound_is_justified(b)),
            upper.filter(|b| self.bound_is_justified(b)),
        ))
    }

    /// `lra.var_bounds_with_reasons` (internal-variable keyed, reaches slack
    /// variables), with an unjustified side reported as absent.
    pub(crate) fn justified_var_bounds_ref(
        &self,
        var: u32,
    ) -> Option<(Option<&Bound>, Option<&Bound>)> {
        let (lower, upper) = self.lra.var_bounds_with_reasons(var)?;
        Some((
            lower.filter(|b| self.bound_is_justified(b)),
            upper.filter(|b| self.bound_is_justified(b)),
        ))
    }

    /// `lra.get_var_bounds` (values only), with an unjustified side reported
    /// as absent.
    pub(crate) fn justified_var_bounds(
        &self,
        var: u32,
    ) -> Option<(Option<BigRational>, Option<BigRational>)> {
        let (lower, upper) = self.justified_var_bounds_ref(var)?;
        Some((lower.map(Bound::value_big), upper.map(Bound::value_big)))
    }

    /// Exit guard for `check()` / `check_during_propagate()`
    /// (#nia-sign-cut-soundness): an `Unsat` whose literals are not all
    /// live asserted atoms is never published — it is downgraded to
    /// `Unknown` and counted in `lia_unjustified_conflicts`.
    ///
    /// Such a conflict is not a valid clause for the current assignment: a
    /// literal that is a bare variable / monomial term (an NIA tentative
    /// bound's reason, carried into the conflict by a bound-reason
    /// collector) or a literal backtracking already retracted cannot be
    /// negated into a learned clause, and the DPLL layer would either drop
    /// the clause (`Unmapped`) or learn one stronger than the theory proved.
    /// The per-site justified-bound reads above keep such literals out of
    /// the conflicts they build; this guard is the invariant, stated once,
    /// for every site — including any that a future reader adds.
    ///
    /// Completeness: sentinel literals are skipped (as everywhere), and a
    /// literal live on any of the three trails passes, so a genuine conflict
    /// is never refused. In a conflict PROBE the placeholders of the probe's
    /// own hypotheses pass too ([`Self::probe_conflict_rests_on_hypotheses`]).
    pub(crate) fn refuse_unjustified_conflict(&mut self, result: TheoryResult) -> TheoryResult {
        let lits: &[TheoryLit] = match &result {
            TheoryResult::Unsat(lits) => lits,
            TheoryResult::UnsatWithFarkas(conflict) => &conflict.literals,
            _ => return result,
        };
        if self.conflict_reasons_all_live(lits) || self.probe_conflict_rests_on_hypotheses(lits) {
            return result;
        }
        self.unjustified_conflicts_dropped += 1;
        if self.debug_lia_check {
            safe_eprintln!(
                "[LIA] refusing to publish a conflict that cites a literal which is not a live \
                 asserted atom ({} lits) — returning Unknown (#nia-sign-cut-soundness)",
                lits.len()
            );
        }
        TheoryResult::Unknown
    }

    /// Whether this solver is a conflict PROBE and every literal of `lits` is
    /// live, a sentinel, or the placeholder `(lhs, true)` of a reasonless
    /// shared equality the probe holds, outside any NIA guess scope
    /// (#probe-hypothesis-premise).
    ///
    /// `probe_needed_shared_equalities` asks a throwaway probe whether the
    /// conflict literals plus a set of candidate shared equalities are
    /// infeasible, and `build_conflict_probe` asserts those candidates WITHOUT
    /// reasons, so their bounds cite the placeholder. Those bounds are
    /// justified (`bound_is_justified`), so an integer side check that folds
    /// one names the placeholder in its conflict. The probe's answer is only
    /// read as a verdict (`probe_verdict_is_unsat`), and the caller appends the
    /// chosen equalities' own reasons, which it requires to be non-empty and
    /// live. So a placeholder in a probe's conflict names a hypothesis the
    /// caller asked about and accounts for, not a guess.
    ///
    /// Refusing those conflicts (as the exit guard did from `bff0049422` on)
    /// made such probes answer `Unknown`: the subset scan could not prove the
    /// equalities an integer refutation needs, and the augmented conflict fell
    /// back to the whole shared-equality closure. On `im_275_asis` that weaker
    /// clause cost `--z3-mode` its `sat` on checks 2-3. The placeholder test is
    /// the one `bound_is_justified` applies: while an NIA guess scope is open a
    /// guess on `lhs` cites the same term, so nothing passes here then. Outside
    /// probes the guard is unchanged.
    fn probe_conflict_rests_on_hypotheses(&self, lits: &[TheoryLit]) -> bool {
        self.conflict_probe
            && lits.iter().all(|lit| {
                lit.term.is_sentinel()
                    || (lit.value && self.is_reasonless_shared_placeholder(lit.term))
                    || self.conflict_reasons_all_live(std::slice::from_ref(lit))
            })
    }

    /// The reason literals of a JUSTIFIED, nameable LRA bound; `None` when
    /// the bound is unjustified or has no nameable reason. Verdict-producing
    /// callers that used `nameable_lra_bound_reasons` alone would accept a
    /// model-derived pin (its reason IS nameable — it is the variable term)
    /// and cite a non-atom in the conflict.
    pub(crate) fn justified_lra_bound_reasons(&self, bound: &Bound) -> Option<Vec<TheoryLit>> {
        if !self.bound_is_justified(bound) {
            return None;
        }
        Self::nameable_lra_bound_reasons(bound)
    }
}
