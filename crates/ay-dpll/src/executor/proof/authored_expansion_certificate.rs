// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The UNSAT EXPANSION CERTIFICATE of the nested-CEGQI quantified-LRA search
//! (#qlra-nested-cegqi, plan §4.1, milestone M3a).
//!
//! A nested `unsat` is a claim about the search's own approximations Γ. It
//! publishes only through this PRODUCER, which proves the authored roots
//! inconsistent from scratch and hands the result to the unchanged strict
//! installation boundary:
//!
//! 1. the lemma plan (`executor::expansion::lemma_plan`) turns Γ into
//!    TAUTOLOGICAL lemma clauses over authored-surface quantifiers (L1
//!    `forall_inst`, L2 `qnt_neg_exists` + `forall_inst`, L3/L4 `sko`);
//! 2. every maximal quantified subterm of `roots ∪ lemmas` becomes a fresh
//!    Boolean proxy ([`super::proxy_renaming`]), and the round trip
//!    `rename(proxy(t)) == t` is checked for every probe assertion;
//! 3. a disposable same-context ground probe must refute the proxied set with
//!    a proof its OWN strict checker accepts complete;
//! 4. the probe proof is renamed back (a theory step naming a proxy refuses)
//!    and stitched: each probe `assume` becomes an authored `assume`, an
//!    `and_pos` projection of one, or its lemma's derivation;
//! 5. the candidate is installed only through
//!    [`Executor::install_strict_authored_candidate`] (reachable assumes are
//!    exact authored roots, empty clause, strict check complete, internal
//!    check). The ordinary mandatory mint re-checks it before publication.
//!
//! Nothing produced here is trusted: a wrong plan, proxy map or stitch can
//! only yield a candidate the boundary refuses, and the verdict then stays
//! the `unknown` it was. The stitch deliberately passes an unrecognized
//! `assume` through unchanged so that refusal is the checker's, not ours.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::time::Instant;
use ay_core::{Proof, TermId};

use super::authored_consequence_replay::InstallRefusal;
use super::proxy_renaming::{ProxyRenaming, RenameDecline};
use crate::cegqi::lra_nested::approx::NInstance;
use crate::cegqi::lra_nested::ntree::NestedTree;
use crate::executor::expansion::lemma_plan::{build_lemma_plan, LemmaPlan, PlanDecline};
use crate::executor::quantifier_loop::result_mapping::{
    SameContextProbeOutcome, SameContextWindow,
};
use crate::executor::Executor;

/// Steps a probe proof may carry into the stitch.
pub(in crate::executor) const MAX_EXPANSION_PROOF_STEPS: usize = 500_000;

/// Sizes and wall times of one certificate attempt (`--stats`).
#[derive(Clone, Debug, Default)]
pub(in crate::executor) struct ExpansionCertReport {
    pub(in crate::executor) lemmas: usize,
    pub(in crate::executor) proxies: usize,
    pub(in crate::executor) steps: usize,
    /// Wall of the ground probe (solve plus its own strict check).
    pub(in crate::executor) probe_ms: u64,
    /// Wall of the installation boundary's strict and internal checks.
    pub(in crate::executor) check_ms: u64,
}

/// Why no certificate was installed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum CertDecline {
    /// The strict check's problem obligation does not yet hold every
    /// authored root (competition shedding's first pass).
    ScopePending,
    Plan(PlanDecline),
    /// Γ produced no lemma: the refutation is the ground roots' own.
    NoLemmas,
    /// A root or lemma the proxy rebuild does not model.
    Proxy,
    /// `rename(proxy(t)) != t` for some probe assertion.
    RoundTrip,
    /// The probe did not refute (sat, unknown, budget, stop).
    Probe,
    /// The probe refuted but produced no strict-complete proof.
    ProbeUnpromotable,
    ProbeSteps,
    Rename(RenameDecline),
    Stitch,
    Install(InstallRefusal),
}

impl CertDecline {
    pub(in crate::executor) fn label(self) -> &'static str {
        match self {
            Self::ScopePending => "scope-pending",
            Self::Plan(plan) => plan.label(),
            Self::NoLemmas => "no-lemmas",
            Self::Proxy => "proxy",
            Self::RoundTrip => "proxy-round-trip",
            Self::Probe => "probe",
            Self::ProbeUnpromotable => "probe-unpromotable",
            Self::ProbeSteps => "probe-steps",
            Self::Rename(rename) => rename.label(),
            Self::Stitch => "stitch",
            Self::Install(refusal) => refusal.label(),
        }
    }
}

#[path = "authored_expansion_certificate/stitch.rs"]
mod stitch;
use stitch::{ConstantFacts, StitchSources};

#[cfg(test)]
#[path = "authored_expansion_certificate/mutation.rs"]
mod mutation;
#[cfg(test)]
use mutation::{mutation, ExpansionCertMutation as Mutation};
#[cfg(test)]
pub(crate) use mutation::{set_expansion_cert_mutation, ExpansionCertMutation};

fn elapsed_ms(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX)
}

/// The proxied probe set of one certificate.
struct ProbeSet {
    /// The exact roots and lemma terms, in probe order.
    originals: Vec<TermId>,
    /// Their proxied forms plus the constant-atom unit facts.
    assertions: Vec<TermId>,
    constants: ConstantFacts,
}

impl Executor {
    /// Build the expansion certificate of the nested search's UNSAT over the
    /// exact authored scope (the roots `tree` was built from) and install it
    /// as `last_proof`. `Ok` only when the strict installation boundary
    /// accepted it; on `Err` all proof state is as found (the caller rolls
    /// the minted terms back).
    ///
    /// The strict check reads its problem obligation from the proof export
    /// scope, which under competition shedding does not hold the authored
    /// roots yet: a candidate assuming them is refused for sure (`assumes
    /// term outside the supplied problem obligation`). The candidate is then
    /// still built, pre-checked and handed back through `deferred` for the
    /// trace-armed retry to install
    /// ([`Self::install_deferred_expansion_certificate`]).
    pub(in crate::executor) fn install_qlra_expansion_certificate(
        &mut self,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        probe_budget_ms: u64,
        report: &mut ExpansionCertReport,
        deferred: &mut Option<Proof>,
    ) -> Result<(), CertDecline> {
        let authored = self.exact_concrete_authored_scope();
        let scope_pending = !self.expansion_obligation_holds(&authored);
        let plan = build_lemma_plan(&mut self.ctx.terms, tree, gamma, &authored)
            .map_err(CertDecline::Plan)?;
        report.lemmas = plan.lemmas.len();
        if plan.lemmas.is_empty() {
            return Err(CertDecline::NoLemmas);
        }
        #[cfg(test)]
        let plan = self.mutated_expansion_plan(plan);
        let mut renaming = ProxyRenaming::default();
        #[cfg(test)]
        {
            renaming.lossy_rename =
                matches!(mutation(), Mutation::LossyProxy | Mutation::DropRoundTrip);
        }
        let set = self.expansion_probe_set(&authored, &plan, &mut renaming)?;
        report.proxies = renaming.len();
        #[cfg(test)]
        let check_round_trip = mutation() != Mutation::DropRoundTrip;
        #[cfg(not(test))]
        let check_round_trip = true;
        if check_round_trip {
            self.check_proxy_round_trip(&set.originals, &mut renaming)?;
        }
        let probe = self.run_expansion_probe(&set.assertions, probe_budget_ms, report)?;
        let renamed = renaming
            .rename_proof(&mut self.ctx.terms, &probe)
            .map_err(CertDecline::Rename)?;
        let sources = StitchSources {
            authored: &authored,
            lemmas: &plan.lemmas,
            constants: &set.constants,
        };
        let candidate = self
            .stitch_expansion_certificate(&renamed, &sources)
            .ok_or(CertDecline::Stitch)?;
        report.steps = candidate.steps.len();
        let started = Instant::now();
        if scope_pending {
            if self.expansion_candidate_plausible(&candidate, &authored) {
                *deferred = Some(candidate);
            }
            report.check_ms = elapsed_ms(started);
            return Err(CertDecline::ScopePending);
        }
        let installed = self.install_strict_authored_candidate(candidate);
        report.check_ms = elapsed_ms(started);
        installed.map_err(CertDecline::Install)
    }

    /// Proxy every root and lemma, and add the constant-atom unit facts.
    fn expansion_probe_set(
        &mut self,
        authored: &[TermId],
        plan: &LemmaPlan,
        renaming: &mut ProxyRenaming,
    ) -> Result<ProbeSet, CertDecline> {
        let originals: Vec<TermId> = authored
            .iter()
            .copied()
            .chain(plan.lemmas.iter().map(|lemma| lemma.term))
            .collect();
        let mut assertions: Vec<TermId> = Vec::with_capacity(originals.len());
        for &original in &originals {
            let proxied = renaming
                .proxy(&mut self.ctx.terms, original)
                .ok_or(CertDecline::Proxy)?;
            if !assertions.contains(&proxied) {
                assertions.push(proxied);
            }
        }
        for fact in renaming.constant_facts(&mut self.ctx.terms) {
            if !assertions.contains(&fact) {
                assertions.push(fact);
            }
        }
        // The renamed form of each constant fact, with its atom and value.
        let mut constants = ConstantFacts::default();
        for (_, atom, truth) in renaming.constants().to_vec() {
            let fact = if truth {
                atom
            } else {
                self.ctx.terms.mk_not_raw(atom)
            };
            constants.insert(fact, (atom, truth));
        }
        for lemma in &plan.lemmas {
            tracing::trace!(
                target: "ay::qlra",
                "cert lemma {:?}: {}",
                lemma.kind,
                ay_proof::render_term_canonical(&self.ctx.terms, lemma.term)
            );
        }
        Ok(ProbeSet {
            originals,
            assertions,
            constants,
        })
    }

    /// `rename(proxy(t)) == t` for every root and lemma.
    fn check_proxy_round_trip(
        &mut self,
        originals: &[TermId],
        renaming: &mut ProxyRenaming,
    ) -> Result<(), CertDecline> {
        for &original in originals {
            let proxied = renaming
                .proxy(&mut self.ctx.terms, original)
                .ok_or(CertDecline::Proxy)?;
            if renaming.rename(&mut self.ctx.terms, proxied) != Some(original) {
                return Err(CertDecline::RoundTrip);
            }
        }
        Ok(())
    }

    /// The disposable same-context ground probe over the proxied set; its
    /// refutation is returned only when its OWN strict checker accepted it
    /// complete.
    fn run_expansion_probe(
        &mut self,
        assertions: &[TermId],
        probe_budget_ms: u64,
        report: &mut ExpansionCertReport,
    ) -> Result<Proof, CertDecline> {
        let started = Instant::now();
        // The probe ingests the instance bodies' undistributed arithmetic
        // as is (see `Executor::proof_probe_skips_som`).
        let skips_som = std::mem::replace(&mut self.proof_probe_skips_som, true);
        let outcome = self.checked_same_context_unsat_proof(
            assertions,
            SameContextWindow::Ground,
            Some(probe_budget_ms),
            None,
            true,
        );
        self.proof_probe_skips_som = skips_som;
        report.probe_ms = elapsed_ms(started);
        let probe = match outcome {
            SameContextProbeOutcome::Proof(proof) => proof,
            SameContextProbeOutcome::UnsatUnpromotable => {
                return Err(CertDecline::ProbeUnpromotable)
            }
            SameContextProbeOutcome::Other => return Err(CertDecline::Probe),
        };
        if probe.steps.len() > MAX_EXPANSION_PROOF_STEPS {
            return Err(CertDecline::ProbeSteps);
        }
        Ok(probe)
    }

    /// A HINT-ONLY pre-check of a candidate that cannot be installed yet
    /// (nothing installed, nothing published): the reachable assumes are
    /// exact authored roots, the empty clause is derived, and every step
    /// strict-checks with those assumes taken as premises.
    fn expansion_candidate_plausible(&self, candidate: &Proof, authored: &[TermId]) -> bool {
        ay_proof::validate_reachable_assumes_in_problem_scope(candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(candidate)
            && self
                .check_proof_strict_derivation_with_datatypes(candidate)
                .is_ok_and(|quality| quality.is_complete())
    }

    /// Whether the strict check's problem obligation holds every authored
    /// root.
    pub(in crate::executor) fn expansion_obligation_holds(&self, authored: &[TermId]) -> bool {
        let obligation: HashSet<TermId> = self
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .collect();
        authored.iter().all(|root| obligation.contains(root))
    }

    /// Install a candidate an earlier pass of THIS public solve built and
    /// parked (`deferred` above) through the same strict installation
    /// boundary, once the problem obligation holds the authored roots.
    ///
    /// The candidate is taken out of `parked` only when the obligation
    /// holds. A pass whose obligation still lacks the authored roots (an
    /// internal retry that is not the trace-armed one, such as the deep-QE
    /// `Unknown` retry) leaves it parked for the pass that can install it:
    /// consuming it there used to drop a certificate the trace-armed retry
    /// would have installed (measured: mjollnir3/formula_030 and
    /// mjollnir6/formula_022 under `--z3-mode`).
    pub(in crate::executor) fn install_deferred_expansion_certificate(
        &mut self,
        parked: &mut Option<Proof>,
        report: &mut ExpansionCertReport,
    ) -> Result<(), CertDecline> {
        let authored = self.exact_concrete_authored_scope();
        if !self.expansion_obligation_holds(&authored) {
            return Err(CertDecline::ScopePending);
        }
        let Some(candidate) = parked.take() else {
            return Err(CertDecline::ScopePending);
        };
        report.steps = candidate.steps.len();
        let started = Instant::now();
        let installed = self.install_strict_authored_candidate(candidate);
        report.check_ms = elapsed_ms(started);
        installed.map_err(CertDecline::Install)
    }
}

#[cfg(test)]
#[path = "authored_expansion_certificate_tests.rs"]
mod tests;
