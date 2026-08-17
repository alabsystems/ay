// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-query isolation and checked result admission for nested probes.

use ay_core::TermId;

use super::{CheckedGroundKind, CheckedGroundScope, CheckedIsolatedMode};
use crate::ematching::contains_quantifier;
use crate::executor::unsat_cert::{probe_cert_reject, UnsatCertificate};
use crate::executor::{Executor, NATIVE_API_ASSERTION_PLACEHOLDER};
use crate::executor_types::SolveResult;

fn report_unsat_decline(token: Option<&UnsatCertificate>, published: bool, checked: bool) {
    if published && checked {
        return;
    }
    // Distinguish publication refusal, stale/missing authority, and a token
    // class this boundary does not admit. Diagnostic only.
    probe_cert_reject(|| {
        let class = match token {
            None => "none",
            Some(certificate) if certificate.strict_proof_verified() => "strict-proof",
            Some(certificate) if certificate.independently_verified() => "independently-checked",
            Some(certificate) if certificate.exact_semantic_verified() => "exact-semantic",
            Some(_) => "competition-raw",
        };
        format!(
            "checked-isolated UNSAT declined: \
             published={published} token={class} checked={checked}"
        )
    });
}

impl Executor {
    /// Install the exact probe roots into a freshly reset probe context the way
    /// the NATIVE API installs an assertion — never by writing
    /// `ctx.assertions` behind the context's back.
    ///
    /// `ResetAssertions` clears `authored_assertions`, `assertions_parsed` and
    /// `assertion_finite_set_metadata`. A raw `probe_ctx.assertions = roots`
    /// then repopulated ONLY the bare term vector, so inside the probe every
    /// authored-provenance question answered "nothing was authored here" while
    /// the working set held N live roots. Two consequences, both real:
    ///
    ///  * `proof_export_scope_assertions` strips the Boolean constant `false`
    ///    out of the strict-proof problem when it is unauthored
    ///    (`#rewritten-constant-premise`), while `authored_corroboration_scope`
    ///    still reads it off `ctx.assertions`. The probe's working set was then
    ///    not a subset of the problem the probe could publish, which is the
    ///    invariant that function's `debug_assert!` polices. The assert is a
    ///    correct gate and this raw write was the lying producer; it reached
    ///    deductive-checks as a `SolverPanic` on the pointer-width loop lanes.
    ///  * `assertion_finite_set_metadata` stayed empty against N assertions,
    ///    breaking the length invariant `push_assertion_stacks` maintains.
    ///
    /// The probe genuinely IS a native-API query: internally-generated exact
    /// roots with no parsed text surface. Recording the
    /// `NATIVE_API_ASSERTION_PLACEHOLDER` for each root is the same route
    /// `Solver::try_assert_term` takes, so `has_authored_surface` stays false
    /// and the existing native carve-out branch runs exactly as before.
    ///
    /// WHY A `false` ROOT MAY BE INSTALLED UNCONDITIONALLY. That placeholder
    /// also marks each root literal-false-sourced, so a `false` among the roots
    /// gains publication rights inside the probe that
    /// `#rewritten-constant-premise` withholds at the OUTER boundary. That is
    /// correct here, and the asymmetry is the whole point of the guard rather
    /// than a hole in it:
    ///
    ///  1. The guard exists to stop an EXPORTED Alethe artifact carrying
    ///     `(assume t0 false)` that an external checker cannot match against the
    ///     input file (measured at 55e938d90; Carcara rejected it). Nothing the
    ///     probe builds is ever exported — `qpf_probe_executor` returns a fresh
    ///     `Executor` over a CLONED context, and `checked_isolated_solve` drops
    ///     it. Only a `CheckedGroundKind` bit crosses back, bound to the
    ///     enclosing epoch, source stamp, exact ordered roots and term snapshot.
    ///  2. The bit it carries cannot be wrong. The probe decides exactly
    ///     `assertions`, and any set containing `false` is unsatisfiable, so
    ///     letting the probe certify that is confirming a tautology.
    ///  3. It cannot launder authority outward. `boolean_constant_premises_authored()`
    ///     on the enclosing query reads `self.ctx`, which the probe never
    ///     touches, so the outer publication path re-derives its own authority
    ///     from its own authored record exactly as before.
    ///
    /// Withholding it instead is what breaks things: a probe whose entire query
    /// is the single root `false` — the shape the alternation and independent-gate
    /// lanes raise — would strip its own only root and then decide an EMPTY
    /// problem, which is trivially SAT. Measured: gating this install on outer
    /// literal-false authority regressed six `ay-dpll --lib` tests across the
    /// independent-gate, CEGQI-certificate and DT-model-certificate lanes while
    /// fixing nothing the unconditional install does not already fix.
    pub(super) fn install_isolated_probe_roots(
        &self,
        probe_ctx: &mut ay_frontend::Context,
        assertions: &[TermId],
    ) {
        for &root in assertions {
            probe_ctx.add_assertion_with_parsed(
                root,
                ay_frontend::command::Term::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_string()),
            );
        }
    }

    /// Shared isolation/certification transaction for the public ground probe
    /// and this module's quantified-UNSAT theorem probes.
    pub(super) fn checked_isolated_solve(
        &mut self,
        assertions: Vec<TermId>,
        mode: CheckedIsolatedMode,
        budget_ms: u64,
    ) -> Option<(CheckedGroundScope, CheckedGroundKind)> {
        let has_quantifier = assertions
            .iter()
            .any(|&term| contains_quantifier(&self.ctx.terms, term));
        let fragment_mismatch =
            matches!(mode, CheckedIsolatedMode::GroundDecision) && has_quantifier;
        if fragment_mismatch || self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return None;
        }
        let scope = CheckedGroundScope::capture(self, &assertions);
        let mut probe_ctx = self.ctx.clone();
        // Strip the outer query before installing exact roots. The nested
        // proof/source epoch must authenticate this obligation, not objectives,
        // soft constraints, or named-core provenance from the enclosing query.
        if probe_ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .is_err()
        {
            return None;
        }
        self.install_isolated_probe_roots(&mut probe_ctx, &assertions);
        let mut probe = self.qpf_probe_executor(probe_ctx, budget_ms);
        probe.original_problem_had_quantifiers = has_quantifier;
        probe.incremental_mode = false;
        // Prevent exact-UNSAT rescue lanes from recursively validating
        // themselves; ordinary preprocessing/refinement remains enabled.
        if matches!(mode, CheckedIsolatedMode::ExactUnsat) {
            probe.in_alternation_validation = true;
            probe.in_nested_array_residue_probe = true;
        }
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);

        let raw = probe.check_sat();
        probe_cert_reject(|| format!("checked-isolated raw result: {raw:?}"));
        let outcome = match raw.ok()? {
            SolveResult::Sat if matches!(mode, CheckedIsolatedMode::GroundDecision) => probe
                .take_sat_certificate()
                .is_some_and(|certificate| certificate.confirms_sat_emission())
                .then_some(CheckedGroundKind::Sat),
            SolveResult::Sat => None,
            result @ SolveResult::Unsat(_) => {
                let certified = probe.certify_unsat_for_publication(result, &[]);
                let published = certified.is_unsat();
                let token = probe.take_unsat_certificate();
                let checked = token
                    .as_ref()
                    .is_some_and(|certificate| certificate.confirms_checked_unsat_emission());
                report_unsat_decline(token.as_ref(), published, checked);
                (published && checked).then_some(CheckedGroundKind::Unsat)
            }
            SolveResult::Unknown => None,
        };
        drop(probe);
        if self.should_abort_theory_loop()
            || !self.qpf_probe_preflight()
            || !scope.is_current_for(self, &assertions)
        {
            probe_cert_reject(|| {
                format!(
                    "checked-isolated post-probe scope check failed: abort={} preflight={} current={}",
                    self.should_abort_theory_loop(),
                    !self.qpf_probe_preflight(),
                    !scope.is_current_for(self, &assertions)
                )
            });
            return None;
        }
        Some((scope, outcome?))
    }
}
