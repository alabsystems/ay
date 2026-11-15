// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The BvUremBound joint, asked where a pass would pay for an exact divider.
//!
//! Two passes hand an authored `bvurem` obligation to the strict checker as
//! one bit-level lemma ahead of the authored cascade: the residual-trust
//! rescue anchors a refutation that collapsed to one empty-clause trust step
//! on the joint negation of the authored roots (`bv_bitblast_collapse.rs`),
//! and the Generic BV promotion re-derives a refutation the search kept no
//! SAT-level derivation for, the whole query's negation
//! (`reassert_final_promotion_boundaries`). When the abstracted attempt
//! cannot refute that lemma, the checker tries the exact divider, and on a
//! wide divider its sweep spends the whole 200,000-conflict envelope without
//! closing (DR-31). The joint of `urem_bound.rs` closes a remainder-range
//! obligation from the theorem `d = 0 or x % d < d` with the division
//! abstracted, but only the cascade and the final boundary asked it, after
//! that sweep. Measured on 7f0f14325 (release CLI, `x % 1000003 < 1000003`
//! over 40 bits): 32 s with `--proof`, 30.2 s of it the rescue's sweep, and
//! 33 s in the default posture, 30.6 s of it the promotion's; the cascade's
//! joint then closed it in under 2 s.
//!
//! So each pass first asks whether its lemma needs the exact divider at all:
//! an authored assertion applies `bvurem`, the lemma reads one, only the
//! proof producer decides it, and the strict checker refuses it with the
//! exact divider withheld (`ay_proof::without_exact_division`). Only then is
//! the joint asked, deciding with no exact divider either. It is installed
//! only when the strict checker accepts it so and it passes the admission
//! rule of its stage (`GuardedCollapseStage::BeforeExactDivision`): as ahead
//! of the promotion, the incumbent's facts are not settled yet, so the
//! candidate must print clean on its own. The strict check is asked first
//! there: with the division abstracted it costs less than that wire screen,
//! a complete blast of the joint's lemma. Asked the other way round, the
//! screen took most of 14.5 s of model-checker-consumer's QF_AUFBV `four_dividers` row
//! (21.5 s against 9.6 s before) on a joint the check refuses in 0.5 s. The
//! screen renders that lemma only while a document is observable; with none,
//! it reads the lemma as a gap and the stage declines the joint, as the
//! cascade would.
//!
//! A lemma the abstracted attempt refutes is accepted and remembered as
//! accepted, so its pass decides it exactly as before and keeps its
//! certificate: an authored `bvurem` the refutation never needs, as `r = a %
//! 10` beside a 64-bit overflow check, keeps its carcara-valid document. A refusal
//! under the probe is remembered nowhere: a declined joint leaves the pass,
//! its sweep and every later lane, the cascade's joint included, to decide
//! exactly as before.
//!
//! Where the exact divider would have closed the lemma, the joint is now the
//! certificate, as it already was wherever that sweep fails. Both documents
//! print the divider through `bitblast_urem` (`carcara_surface=clean-dialect`,
//! which Carcara 1.1.0 rejects on either side), and the joint's is the
//! smaller: at 32 and 36 bits 2.3 and 2.7 MB against 11 and 15 MB. The
//! best-effort default certificate's emission budget refuses the joint's from
//! 32 bits (two remainders: from 24), so such a bound now answers in about
//! 1 s in the default posture with no default document, where its sweep
//! closed in 6 to 23 s and published one of 10 to 19 MB; `--proof` and
//! `--strict-proofs` print the joint's. Nothing new is interned for any other
//! query.

use super::*;
use ay_core::kani_compat::DetHashSet;
use ay_core::TermData;

#[cfg(test)]
mod tests;

/// Terms the `bvurem` census walks before it gives up (and asks nothing).
const MAX_CENSUS_VISITS: usize = 1 << 16;

impl Executor {
    /// At the residual-trust rescue, before its anchor `anchor` (the joint
    /// negation of the authored roots): whether the joint replaced `proof`,
    /// the single-empty-trust collapse.
    pub(in crate::executor::proof) fn promote_urem_bound_before_rescue_anchor(
        &mut self,
        proof: &mut Proof,
        anchor: &[TermId],
    ) -> bool {
        self.asks_urem_bound_before_exact_division()
            && self.needs_exact_divider(anchor)
            && self.promote_urem_bound_before_exact_division(proof, "rescue anchor")
    }

    /// Before the Generic BV promotion: whether the joint replaced `proof`.
    /// The lemmas asked are the ones the promotion hands the proof producer,
    /// in its order and under its bound
    /// (`promote_semantically_checked_bv_lemmas`).
    pub(in crate::executor::proof) fn promote_urem_bound_before_generic_promotion(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        if !self.asks_urem_bound_before_exact_division() {
            return false;
        }
        let mut producer = 0_usize;
        let needs = proof.steps.iter().any(|step| {
            let ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                clause,
                ..
            } = step
            else {
                return false;
            };
            if !ay_proof::bv_bitblast_requires_proof_producer(&self.ctx.terms, clause) {
                return false;
            }
            producer += 1;
            producer <= ay_proof::MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF
                && self.needs_exact_divider(clause)
        });
        needs && self.promote_urem_bound_before_exact_division(proof, "Generic promotion")
    }

    /// The gates the cascade and the final boundary ask the joint under, and
    /// an authored `bvurem`: asked first, they intern and decide nothing.
    fn asks_urem_bound_before_exact_division(&self) -> bool {
        !self.skips_trust_elimination_repairs()
            && self.ctx.assertions_parsed().len() <= MAX_GUARDED_ROOTS
            && self.authored_remainder()
    }

    /// Whether deciding `clause` would pay for an exact divider: it reads a
    /// `bvurem`, only the proof producer decides it, and the strict checker
    /// refuses it with the exact divider withheld. An acceptance here is the
    /// clause's (remembered as such); a refusal is remembered nowhere.
    fn needs_exact_divider(&self, clause: &[TermId]) -> bool {
        mentions_remainder(&self.ctx.terms, clause)
            && ay_proof::bv_bitblast_requires_proof_producer(&self.ctx.terms, clause)
            && !ay_proof::without_exact_division(|| {
                self.recognize_bv_bitblast_until_stopped(clause)
            })
    }

    fn promote_urem_bound_before_exact_division(&mut self, proof: &mut Proof, site: &str) -> bool {
        let mut roots = Vec::new();
        for index in 0..self.ctx.assertions_parsed().len() {
            let Some((root, _, _)) = self.guarded_source_root(index) else {
                return false;
            };
            roots.push(root);
        }
        let stop = self.make_proof_assembly_should_stop();
        let mut incumbent = IncumbentFacts::new(false);
        let replaced = ay_proof::without_exact_division(|| {
            self.promote_urem_bound_joint(
                proof,
                &roots,
                GuardedCollapseStage::BeforeExactDivision,
                &mut incumbent,
                &stop,
            )
        });
        crate::executor::unsat_cert::probe_cert_reject(|| {
            let outcome = match replaced {
                Some(true) => "installed",
                Some(false) => "declined",
                None => "stopped",
            };
            format!("urem-bound joint before the {site}'s exact divider: {outcome}")
        });
        if replaced != Some(true) {
            return false;
        }
        // An authored replacement, as the cascade's joint is
        // (`publish_replacement_over_withheld_derivation`).
        self.publish_replacement_over_withheld_derivation(proof);
        true
    }

    /// Whether an authored assertion, its source macros expanded, applies
    /// `bvurem`. Read off the parsed source: a lemma can read a `bvurem` the
    /// elaborator introduced, and asking costs no interning.
    fn authored_remainder(&self) -> bool {
        self.ctx.assertions_parsed().iter().any(|assertion| {
            source::expand(&self.ctx, assertion)
                .is_some_and(|expanded| applies_remainder(&expanded))
        })
    }
}

/// Whether `root` (an expansion `source::expand` bounded) applies `bvurem`.
fn applies_remainder(root: &FrontendTerm) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        match term {
            FrontendTerm::App(head, _) if head == "bvurem" => return true,
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => pending.extend(args.iter()),
            _ => {}
        }
    }
    false
}

/// Whether a `bvurem` application occurs below `roots` (a bounded walk; past
/// the bound, no).
fn mentions_remainder(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut seen = DetHashSet::default();
    let mut pending = roots.to_vec();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_CENSUS_VISITS {
            return false;
        }
        if matches!(terms.get(term), TermData::App(Symbol::Named(name), _) if name == "bvurem") {
            return true;
        }
        pending.extend(terms.children(term));
    }
    false
}
