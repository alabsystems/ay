// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-query isolation and checked result admission for nested probes.

use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

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

/// AY's marker for an INTERNALLY MINTED symbol. The frontend rejects it in user
/// input (`is_reserved_symbol`), so a symbol spelled with this prefix was
/// minted by AY itself during some solve.
const INTERNAL_SYMBOL_MARKER: &str = "__ay_";

/// Whether `terms` holds an AY-internal symbol whose NAME may carry a
/// `TermId`.
///
/// # The hazard
///
/// Several of AY's internal mints bake a `TermId` INTO THE SYMBOL'S NAME and
/// parse it back out later. The id then travels as TEXT, where no
/// [`ay_core::term::RemapTable`], no `Remappable` visitor and no exhaustive
/// `TermId` walk can see it. `mark_and_compact`'s contract — every external
/// holder is a root or is remapped — is silently violated, and after a
/// relabelling the name denotes a DIFFERENT term, or none at all. Every such
/// mint found by scanning `ay-core`, `ay-frontend` and `ay-dpll` for a symbol
/// name formatted from a `TermId`:
///
///  * `__ay_zerodiv_{op}_{dividend}`, `__ay_symdiv_{kind}_{a}_{b}` —
///    `executor::mod_div_elim`, decoded by `collect_zero_divisor_vars` and by
///    `executor::model::div_witness`;
///  * `__ay_ite_def_{ite}` — `ay_core::term::ite_lifting`, decoded by
///    `executor::proof::ite_definition_leaf`;
///  * `__ay_arrflat!{array}_t{index}` — `executor::theories::fp::flatten_reads`;
///  * `__ay_bv_lia_cong_k{source}_w{width}` — `executor::theories::combined`;
///  * `__ay_native_replay_unauthenticated_{term}` — `api::solving::native_replay`;
///  * the `<prefix><label>!{map}` map-domain carriers in
///    `ay_frontend::elaborate::app::map`, which says outright that the id is
///    parsed back and that `__ay_` is reserved so nothing can collide with it.
///
/// MEASURED, not theorised. Without this veto the `__ay_zerodiv_*` case is a
/// live panic: `ufbv_fixpoint_premise_forced_unsat::
/// underspecified_division_in_premise_is_never_refuted` builds a probe whose
/// arena prunes 131 -> 12 terms while a surviving `__ay_zerodiv_*` name still
/// spells dividend index 56, `collect_zero_divisor_vars` decodes it, and
/// `TermStore::get` panics with `index out of bounds: the len is 15 but the
/// index is 56`. The compacted store is internally consistent at that point
/// (measured: zero dangling children, zero out-of-range roots) — the dangling
/// id is the one that travelled as a string.
///
/// # Why this test and not a list of those six prefixes
///
/// A prefix list is only as good as the next mint that forgets to join it, and
/// a missed entry does not produce a slow probe — it produces a wrong term
/// silently substituted for another. The test is instead a property of the
/// hazard itself: an id baked into a name is SPELLED THERE, so the name
/// contains its decimal digits. Vetoing every internal symbol whose name
/// carries a digit therefore covers every present encoder AND every future one,
/// with no enumeration to keep in step. It also vetoes internal names whose
/// digits are a plain counter rather than an id (`__ay_sk_x!3`); that costs
/// speed and nothing else. Digit-FREE internal names (`__ay_dt_depth_List`, the
/// only one the `inc_some_list` probe carries) cannot be spelling an id and
/// stay prunable.
fn carries_name_encoded_term_ids(terms: &TermStore) -> bool {
    let name_encodes_a_term_id = |name: &str| {
        name.starts_with(INTERNAL_SYMBOL_MARKER) && name.bytes().any(|byte| byte.is_ascii_digit())
    };
    (0..terms.len()).any(|index| {
        let Ok(raw) = u32::try_from(index) else {
            return false;
        };
        match terms.get(TermId(raw)) {
            TermData::Var(name, _) => name_encodes_a_term_id(name),
            TermData::App(Symbol::Named(name) | Symbol::Indexed(name, _), _) => {
                name_encodes_a_term_id(name)
            }
            _ => false,
        }
    })
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

    /// The isolated probe's context: a clone of the enclosing one with the
    /// outer query stripped and the exact roots installed the native-API way.
    ///
    /// Split out of [`Self::checked_isolated_solve`] so the pruned build below
    /// has an exact, unpruned twin to fall back to.
    fn isolated_probe_context(&self, assertions: &[TermId]) -> Option<ay_frontend::Context> {
        let mut probe_ctx = self.ctx.clone();
        // Strip the outer query before installing exact roots. The nested
        // proof/source epoch must authenticate this obligation, not objectives,
        // soft constraints, or named-core provenance from the enclosing query.
        probe_ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .ok()?;
        self.install_isolated_probe_roots(&mut probe_ctx, assertions);
        Some(probe_ctx)
    }

    /// The same probe context with the cloned arena rebuilt around THIS query.
    ///
    /// # Why the clone alone is not enough
    ///
    /// The clone is deliberate and stays — a thin re-translate of the roots
    /// alone leaves deep nested-`ite` obligations `Unknown`, which is the
    /// documented reason `Context` is `Clone` at all. What must not come with
    /// it is the enclosing solve's SCRATCH: every quantifier instance, theory
    /// lemma and proof-planning bridge node the OUTER solve hash-consed into
    /// the live arena. Nothing asserts them and this obligation cannot reach
    /// them, but whole-store scans inside the probe still see them, and the
    /// probe's own completeness ledgers are what those scans feed.
    ///
    /// Measured on the `inc_some_list` dual-vocabulary datatype obligation
    /// (`dt_uf_bridge_congruence::inc_some_list_dual_vocab_obligation_is_unsat`).
    /// Its 52-root authored ground core reaches this probe carrying an arena of
    /// **353,363** terms, of which the core reaches **199** — 0.06%. On the
    /// unpruned clone `solve_with_dt_axioms` failed closed on its deterministic
    /// budget and the probe answered `Ok(Unknown)`, so the authored-ground-core
    /// leg declined a refutation the probe can actually reach. On the pruned
    /// clone the same probe answers `Ok(Unsat(..))` with its build phase sealed
    /// at 13.9ms. The store size was the cause, not the clock: this leg's wall
    /// budget was unchanged across both measurements.
    ///
    /// # The pruning rule, and why it cannot drop something the probe needs
    ///
    /// [`ay_frontend::Context::compact_terms_for_derived_query`] marks from
    /// EVERY `TermId` the context itself still holds — not from the roots
    /// alone — plus the `TermStore`-owned pins (`true`, `false`, and every
    /// entry in `TermStore::names`). Reachability is the real term DAG
    /// (`TermStore::for_each_child`, which is also what the child-rewrite pass
    /// uses, so marking and rewriting cannot drift), extended with the
    /// `:no-pattern` side map. So the survivors include, without this call
    /// having to enumerate them:
    ///
    ///  * the installed roots and their transitive closure, because
    ///    `install_isolated_probe_roots` ran FIRST — hence the ordering here;
    ///  * every declared symbol's term, via `Context::symbols`,
    ///    `Context::overloaded_symbols`, `Context::datatype_member_symbols`
    ///    and `TermStore::names`, whether or not any root mentions it;
    ///  * every nullary constructor term, adopted-macro body, named term and
    ///    scope-frame binding the context still holds.
    ///
    /// Anything the probe MINTS later — datatype axioms, quantifier instances,
    /// skolems, definitional extensions — is interned fresh into the rebuilt
    /// hash-cons map, so it cannot be a term this pass could have reclaimed.
    /// Anything the probe RE-ELABORATES (`define-fun` bodies, schematic
    /// assertions) is a parser AST, not a `TermId`, and re-elaborates into the
    /// same interned node. What is left over — a node no root reaches and no
    /// symbol, name, scope or macro names — is unreachable from the probe by
    /// construction: the probe has no `TermId` of its own (`qpf_probe_executor`
    /// copies only scalar resource settings), so `probe.ctx` is the ONLY way it
    /// can name a term.
    ///
    /// Survivors keep byte-identical `TermData` and their `TermEntry` stamp;
    /// only ids move, and they move through the `RemapTable` the same in-place
    /// relabelling produced. So this cannot change a verdict the probe would
    /// otherwise reach on the merits, and it cannot let the probe accept
    /// something it should refuse: the probe still has to publish and
    /// self-check its own certificate, and the outer authority binding
    /// (`CheckedGroundScope`) is captured on `self.ctx`, which this never
    /// touches.
    ///
    /// # Fail closed
    ///
    /// The rebuild is all-or-nothing: it returns `false` if any held id could
    /// not be translated, and a partially relabelled context must never be
    /// solved. This does NOT decline the probe — it rebuilds the exact
    /// unpruned clone the probe had before this existed and runs that, so a
    /// query shape whose arena cannot be rebuilt is merely as slow as it
    /// always was.
    fn pruned_isolated_probe_context(&self, assertions: &[TermId]) -> Option<ay_frontend::Context> {
        let mut probe_ctx = self.isolated_probe_context(assertions)?;
        let before = probe_ctx.terms.len();
        if carries_name_encoded_term_ids(&probe_ctx.terms) {
            probe_cert_reject(|| {
                format!(
                    "checked-isolated probe arena NOT pruned at {before} terms: \
                     an AY-internal symbol name may spell a TermId"
                )
            });
            return Some(probe_ctx);
        }
        if probe_ctx.compact_terms_for_derived_query() {
            probe_cert_reject(|| {
                format!(
                    "checked-isolated probe arena: {before} -> {} terms",
                    probe_ctx.terms.len()
                )
            });
            return Some(probe_ctx);
        }
        probe_cert_reject(|| {
            format!(
                "checked-isolated probe arena rebuild DECLINED at {before} terms; \
                 falling back to the unpruned clone"
            )
        });
        self.isolated_probe_context(assertions)
    }

    /// One satisfying assignment's concrete values for `targets`, or `None`.
    ///
    /// NO AUTHORITY CROSSES THIS BOUNDARY, BY CONSTRUCTION. Unlike
    /// [`Self::checked_isolated_solve`], this probe returns no
    /// `CheckedGroundKind` and no sealed scope — only plain `EvalValue` data.
    /// It is deliberately usable ONLY where a wrong answer is harmless.
    ///
    /// Its sole caller is the finite-sort model-refinement lane
    /// (`executor/finite_model_mbqi.rs`), which turns each returned value into
    /// a ground INSTANCE `body[x := v]` of a conjunctive-position `forall`.
    /// `forall x. body |= body[x := v]` holds for EVERY ground `v`, so an
    /// instance built from a stale, arbitrary, or outright wrong value is still
    /// a sound logical consequence of an asserted universal: the worst a bad
    /// witness can do is waste a refinement round. That is why this probe may
    /// read the nested model directly while the SAT/UNSAT decisions of the same
    /// lane must go through `checked_ground_solve`.
    ///
    /// Quantified assertions are refused: a nested quantifier would make the
    /// probe's own verdict a quantifier problem rather than the bit-blastable
    /// counterexample search this is for.
    pub(in crate::executor) fn probe_finite_witness_values(
        &mut self,
        assertions: Vec<TermId>,
        targets: &[TermId],
        budget_ms: u64,
    ) -> Option<Vec<crate::executor::model::EvalValue>> {
        if targets.is_empty() || self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return None;
        }
        if assertions
            .iter()
            .any(|&term| contains_quantifier(&self.ctx.terms, term))
        {
            return None;
        }
        // DELIBERATELY UNPRUNED. Unlike every other probe here, this one
        // evaluates `targets` — ids minted in the ENCLOSING store — against the
        // probe's model. Rebuilding the arena relabels ids, so a pruned context
        // would read those ids as different terms (or out of range). Pruning
        // this probe needs the remap table applied to `targets`, which
        // `compact_terms_for_derived_query` does not hand back; until it does,
        // this site keeps the clone it always had.
        let probe_ctx = self.isolated_probe_context(&assertions)?;
        let mut probe = self.qpf_probe_executor(probe_ctx, budget_ms);
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        let values = match probe.check_sat() {
            Ok(SolveResult::Sat) => probe.last_model.as_ref().map(|model| {
                targets
                    .iter()
                    .map(|&target| probe.evaluate_term(model, target))
                    .collect::<Vec<_>>()
            }),
            _ => None,
        };
        drop(probe);
        values
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
        let probe_ctx = self.pruned_isolated_probe_context(&assertions)?;
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

#[cfg(test)]
#[path = "checked_isolated_solve_tests.rs"]
mod tests;
