// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hypothesis scopes of the active public UNSAT query, for authority legs that
//! RE-DECIDE a subset of them in isolation.
//!
//! Two accessors, one entailment. Both answer "which formulas may a disposable
//! probe assume?", and both rest on the same fact: refuting any SUBSET of a
//! query's hypotheses refutes the query, because dropping hypotheses only
//! weakens. They differ only in how much of the query they are willing to
//! recognise as hypotheses.

use super::*;

impl Executor {
    /// The AUTHORED hard-assertion roots of the current public UNSAT query, for
    /// callers that will RE-DECIDE a subset of them in isolation.
    ///
    /// This keeps every scope conjunct of
    /// [`Self::exact_plain_hard_unsat_scope_is_current`] that bears on whether
    /// the verdict rests on authored HARD assertions alone — same epoch, no
    /// assumptions, no declared extensions or objectives — and deliberately
    /// drops the two that compare the LIVE working window
    /// (`epoch.assertions == ctx.assertions` and the matching proof-provenance
    /// equality).
    ///
    /// Dropping them is sound here and only here: those conjuncts exist so a
    /// Skolemized/instantiated window cannot acquire SOURCE authority by shape
    /// coincidence, whereas this accessor's callers take no authority from the
    /// live window at all — they re-solve the authored roots from scratch on a
    /// disposable executor, and that probe re-binds epoch, source stamp, ordered
    /// roots, and term snapshot itself. Inside the quantifier loop the window
    /// has necessarily been rewritten, so requiring equality would make the
    /// accessor unconditionally `None` exactly where it is needed.
    pub(in crate::executor) fn authored_hard_unsat_roots_for_isolated_recheck(
        &self,
    ) -> Option<Vec<TermId>> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        let no_assumptions = epoch
            .assumptions
            .as_deref()
            .is_none_or(<[TermId]>::is_empty);
        if !(epoch.is_current(self)
            && no_assumptions
            && epoch.declared_extension.is_empty()
            && epoch.declared_extension_entries.is_empty()
            && epoch.declared_extension_objectives.is_none()
            && epoch.declared_extension_objective_entries.is_none())
        {
            return None;
        }
        if self.last_assumptions.iter().flatten().next().is_some() {
            return None;
        }
        Some(epoch.assertions.clone())
    }

    /// Every HYPOTHESIS of the current public UNSAT query — the authored hard
    /// roots of the bound epoch UNIONED with the exact assumption vectors — for
    /// callers that will RE-DECIDE a SUBSET of them in isolation.
    ///
    /// # Why this exists (#uc-named-core-ground-scope)
    ///
    /// [`Self::authored_hard_unsat_roots_for_isolated_recheck`] answers `None`
    /// the moment ANY assumption is live, because `epoch.assertions` alone is
    /// then not the whole query. That is the right answer for a caller that
    /// needs the EXACT query. It is the wrong answer for a caller that only
    /// needs formulas the query ENTAILS, and it silently disabled that whole
    /// family of authority legs for `:produce-unsat-cores` scripts — where the
    /// named-core redirect re-routes `(check-sat)` through `check-sat-assuming`
    /// with the authored NAMED ASSERTIONS THEMSELVES as the assumption vector
    /// (see `last_core_term_to_name`). Nothing new is assumed there; the same
    /// authored formulas are merely also named as assumptions so the SAT layer
    /// can report which of them participated.
    ///
    /// Measured on the verification-consumer `inc_some_list` obligation
    /// (`dt_uf_bridge_congruence_inc_some_list.smt2`): `epoch.assertions` = 111,
    /// `epoch.assumptions` = 0 (bound empty), `last_assumptions` = 111 — of
    /// which 106 are literally authored roots and 5 are the per-assertion
    /// EQUIVALENT rewrites `#uc-named-provenance` lets a label ride. The sibling
    /// accessor answered `None` purely on "an assumption is live", so
    /// `--debug-cert` reported `CERT/ground-core decline: no authored hard
    /// scope`: the ground-core authority leg never ran at all, on a query whose
    /// hypotheses included every authored root.
    ///
    /// # Soundness
    ///
    /// `check-sat-assuming(A)` over assertion stack `S` decides `⋀S ∧ ⋀A`, so
    /// every member of `S ∪ A` is a HYPOTHESIS of the exact query being decided.
    /// Refuting any SUBSET of a hypothesis set refutes the query — the identical
    /// entailment the sibling accessor's callers already rely on; this one
    /// merely stops discarding half the hypotheses. It grants no authority by
    /// itself: callers re-solve the chosen subset from scratch on a disposable
    /// executor that re-binds its own epoch, source stamp, ordered roots and
    /// term snapshot, and the enclosing publication funnel still mints or
    /// refuses the token.
    ///
    /// Fails closed on a stale epoch, on any declared obligation extension or
    /// objective, and on an UNBOUND assumption vector — an epoch that never
    /// passed through a public wrapper, whose shape `is_current` therefore never
    /// stamp-checked.
    pub(in crate::executor) fn authored_hard_unsat_hypotheses_for_isolated_recheck(
        &self,
    ) -> Option<Vec<TermId>> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        if !(epoch.is_current(self)
            && epoch.declared_extension.is_empty()
            && epoch.declared_extension_entries.is_empty()
            && epoch.declared_extension_objectives.is_none()
            && epoch.declared_extension_objective_entries.is_none())
        {
            return None;
        }
        let bound = epoch.assumptions.as_deref()?;
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        let mut hypotheses = Vec::with_capacity(epoch.assertions.len() + bound.len());
        for &term in epoch
            .assertions
            .iter()
            .chain(bound)
            .chain(self.last_assumptions.iter().flatten())
        {
            if seen.insert(term) {
                hypotheses.push(term);
            }
        }
        (!hypotheses.is_empty()).then_some(hypotheses)
    }
}

#[cfg(test)]
mod tests {
    use crate::executor::Executor;

    /// RED->GREEN pin for #uc-named-core-ground-scope.
    ///
    /// The named-core redirect leaves the authored roots in the epoch AND
    /// re-supplies them (plus their equivalent rewrites) as the live assumption
    /// vector. The strict accessor must keep refusing — it promises the EXACT
    /// query and an assumption vector is live — while the hypothesis accessor
    /// must return every hypothesis, so the ground-core authority leg can run.
    ///
    /// MUTATION: drop the `.chain(self.last_assumptions...)` term and this
    /// fails on the rewritten assumption; return `epoch.assertions.clone()`
    /// unconditionally and the strict-accessor assertion below fails.
    #[test]
    fn named_core_assumptions_are_hypotheses_even_though_the_strict_scope_refuses() {
        let mut executor = Executor::new();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("uc_named_core_root", ay_core::Sort::Bool);
        let rewritten = executor
            .ctx
            .terms
            .mk_fresh_var("uc_named_core_rewritten", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![root];
        executor.begin_unsat_query_epoch(&[root]);
        executor.bind_unsat_query_assumptions(&[]);
        // The named-core redirect's live assumption vector: the authored root
        // itself, plus the per-assertion equivalent rewrite of another one.
        executor.last_assumptions = Some(vec![root, rewritten]);

        assert_eq!(
            executor.authored_hard_unsat_roots_for_isolated_recheck(),
            None,
            "the strict accessor promises the exact query and must still refuse \
             once any assumption is live"
        );
        assert_eq!(
            executor.authored_hard_unsat_hypotheses_for_isolated_recheck(),
            Some(vec![root, rewritten]),
            "every authored root and every live assumption is a hypothesis of \
             the decided query"
        );
    }

    /// The hypothesis accessor is not a way around an UNBOUND epoch: without a
    /// bound assumption vector no public wrapper declared this query's shape,
    /// so `is_current` never stamp-checked one and the leg must fail closed.
    ///
    /// MUTATION: replace `epoch.assumptions.as_deref()?` with
    /// `.unwrap_or_default()` and this returns `Some`.
    #[test]
    fn an_unbound_assumption_vector_yields_no_hypothesis_scope() {
        let mut executor = Executor::new();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("uc_unbound_root", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![root];
        executor.begin_unsat_query_epoch(&[root]);

        assert_eq!(
            executor.authored_hard_unsat_hypotheses_for_isolated_recheck(),
            None,
            "an epoch that never passed a public wrapper has no checked shape"
        );
    }
}
