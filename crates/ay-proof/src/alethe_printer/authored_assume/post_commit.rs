// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Document-rendering bridges re-planned against the view the commit
//! produces.
//!
//! A [`AuthoredAssumeBridge::PrintedEquivalence`] bridge is derived against
//! the DOCUMENT's rendering of its term ([`super::document_canonical`]): the
//! derivation checks every canonical child against the text the document
//! prints for it, and the emitter re-derives it at the `assume`. The planner
//! derives it while every override is still in place, but its own commit then
//! confines every planned term to the text its bridge concludes and drops the
//! assume-only overrides from the document. A bridge that read the override
//! of a term the same planner confines therefore no longer has its derivation
//! when the emitter asks for it. MEASURED at `e9ba9acac` on
//! `(assert (=> (>= y 0) (<= x 3)))` + `(assert (> x 5))` +
//! `(assert (>= y 0))`: the implication was planned onto the document's
//! `(or (<= x 3) (not (>= y 0)))`, the third row then confined `(<= 0 y)` to
//! its canonical text, and the printer refused the publication ("planned
//! authored assume equivalence no longer has a checked derivation"); the
//! `(=> (>= m1 0) (= (* 3 m1) x1))` row of a modular carry chain was refused
//! the same way.
//!
//! So after planning, every such bridge is re-derived under the commit's view
//! (installed and removed again, exactly). A bridge that fails is planned
//! afresh against that view, with every other plan in place; a term no schema
//! bridges there is declined, which leaves its override where it was before
//! any bridge existed. A bounded number of rounds re-checks the bridges a
//! re-plan disturbed; whatever is still stale after them is left to the
//! emitter, which refuses it exactly as before.
//!
//! Only this bridge is re-derived, because only its emitter reads the live
//! document. The other document-rendering bridges
//! ([`AuthoredAssumeBridge::DistinctElimination`],
//! [`AuthoredAssumeBridge::CongruentConjunction`],
//! [`AuthoredAssumeBridge::FoldedDocumentEquivalence`]) also conclude the
//! pre-commit rendering, but re-render from their two planned texts alone, so
//! the emitter never loses them. When the commit's view prints such a term
//! differently in a step that consumes it, the consumer's own validators
//! repair the spelling or refuse the document, as they would without the
//! bridge (MEASURED: `(= (> x 3) false)` beside `(> x 3)` concludes
//! `(not (> x 3))` while the second row prints `(< 3 x)`, and the
//! `la_generic` resolution repair joins them; pinned carcara `valid`).

use super::*;

/// Re-check rounds; past them the emitter judges what is left.
const MAX_STALE_REPLAN_ROUNDS: usize = 4;

/// The channel entries [`AlethePrinter::install_commit_view`] added, so the
/// view can be removed exactly.
struct InstalledCommitView {
    renderings: Vec<TermId>,
    previous_assume_only: HashSet<TermId>,
}

/// The bridged `assume` ids of every planned term, in proof order.
fn bridged_ids_by_term(
    proof: &Proof,
    planner: &AuthoredAssumePlanner,
) -> HashMap<TermId, Vec<ProofId>> {
    let mut ids: HashMap<TermId, Vec<ProofId>> = HashMap::default();
    for (index, step) in proof.steps.iter().enumerate() {
        let id = ProofId(index as u32);
        if let ProofStep::Assume(term) = step {
            if planner.bridged_ids.contains(&id) && planner.planned.contains_key(term) {
                ids.entry(*term).or_default().push(id);
            }
        }
    }
    ids
}

impl AlethePrinter<'_> {
    /// Re-plan every printed-equivalence bridge the commit would leave without
    /// its derivation. Changes nothing when every bridge survives the commit.
    pub(super) fn replan_stale_document_bridges(
        &self,
        proof: &Proof,
        planner: &mut AuthoredAssumePlanner,
    ) -> Result<(), AlethePrintError> {
        if !planner
            .planned
            .values()
            .any(|plan| matches!(plan.bridge, AuthoredAssumeBridge::PrintedEquivalence))
        {
            return Ok(());
        }
        let bridged = bridged_ids_by_term(proof, planner);
        for _ in 0..MAX_STALE_REPLAN_ROUNDS {
            let stale = self.stale_printed_equivalences(planner, &bridged);
            if stale.is_empty() {
                break;
            }
            for term in stale {
                if !self.replan_against_commit_view(term, &bridged, planner) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// The printed-equivalence plans whose bridge the commit's view cannot
    /// re-derive, in term order.
    fn stale_printed_equivalences(
        &self,
        planner: &AuthoredAssumePlanner,
        bridged: &HashMap<TermId, Vec<ProofId>>,
    ) -> Vec<TermId> {
        let view = self.install_commit_view(planner);
        let mut stale = Vec::new();
        for (term, plan) in &planner.planned {
            if !matches!(plan.bridge, AuthoredAssumeBridge::PrintedEquivalence) {
                continue;
            }
            let Some(&id) = bridged.get(term).and_then(|ids| ids.first()) else {
                continue;
            };
            let (rendered, _) = self.render_authored_assume_bridge(
                id,
                *term,
                &plan.surface,
                &plan.canonical,
                plan.bridge,
            );
            if rendered.is_none() {
                stale.push(*term);
            }
        }
        self.remove_commit_view(view);
        stale.sort_unstable();
        stale
    }

    /// Plan `term` afresh under the commit's view of every other plan, or
    /// decline it. Returns `false` (with the original plan restored) when
    /// the re-plan overruns the planner's accounting: the emitter then
    /// judges the original plan exactly as before.
    fn replan_against_commit_view(
        &self,
        term: TermId,
        bridged: &HashMap<TermId, Vec<ProofId>>,
        planner: &mut AuthoredAssumePlanner,
    ) -> bool {
        let (Some(original), Some(ids)) = (planner.planned.remove(&term), bridged.get(&term))
        else {
            return true;
        };
        let view = self.install_commit_view(planner);
        let replanned = self.replan_term(term, ids, &original.surface, planner);
        self.remove_commit_view(view);
        match replanned {
            Ok(Some(plan)) => {
                planner.planned.insert(term, plan);
                true
            }
            Ok(None) => {
                planner.unsupported.insert(term);
                for id in ids {
                    planner.bridged_ids.remove(id);
                }
                true
            }
            Err(_) => {
                planner.planned.insert(term, original);
                false
            }
        }
    }

    /// The planner's own admission of `term` at its first bridged id, then
    /// the use charge of every further id; `None` when either declines.
    fn replan_term(
        &self,
        term: TermId,
        ids: &[ProofId],
        surface: &str,
        planner: &mut AuthoredAssumePlanner,
    ) -> Result<Option<AuthoredAssumePlan>, AlethePrintError> {
        let Some((&first, rest)) = ids.split_first() else {
            return Ok(None);
        };
        let Some(plan) = self.plan_new_authored_assume_term(first, term, surface, planner)? else {
            return Ok(None);
        };
        for &id in rest {
            if !self.plan_authored_assume_use(id, term, &plan, &mut planner.accounting)? {
                return Ok(None);
            }
        }
        Ok(Some(plan))
    }

    /// Install what `commit_authored_assume_plan` will install for the
    /// current plans: each planned term's concluded text, and the assume-only
    /// suppression. Entries another channel already owns are left alone.
    fn install_commit_view(&self, planner: &AuthoredAssumePlanner) -> InstalledCommitView {
        let mut renderings = self.let_bridge_renderings.borrow_mut();
        let mut added = Vec::new();
        for (term, plan) in &planner.planned {
            if !renderings.contains_key(term) {
                renderings.insert(*term, plan.canonical.clone());
                added.push(*term);
            }
        }
        drop(renderings);
        let previous_assume_only = std::mem::replace(
            &mut *self.assume_only_override_terms.borrow_mut(),
            planner.assume_only_terms.clone(),
        );
        self.format_cache.borrow_mut().clear();
        self.charge((added.len() + planner.assume_only_terms.len()) as u64);
        InstalledCommitView {
            renderings: added,
            previous_assume_only,
        }
    }

    fn remove_commit_view(&self, view: InstalledCommitView) {
        let mut renderings = self.let_bridge_renderings.borrow_mut();
        for term in &view.renderings {
            renderings.remove(term);
        }
        drop(renderings);
        *self.assume_only_override_terms.borrow_mut() = view.previous_assume_only;
        self.format_cache.borrow_mut().clear();
    }
}

#[cfg(test)]
#[path = "post_commit_tests.rs"]
mod tests;
