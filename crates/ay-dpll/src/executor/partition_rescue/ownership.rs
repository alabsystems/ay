// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Which partition components own the premises of the proof installed in
//! `last_proof` when a rescue's `unsat` returns.
//!
//! The rescue returns the first `unsat` a component solve returns and leaves
//! `last_proof` as it stands then (`partition_rescue.rs`): the proof that
//! solve installed, when it installed one. The component loop does not clear
//! `last_proof`, so for a solve that returns `unsat` without installing a
//! proof (the pigeonhole arm of `Executor::solve_partition_component` is
//! one) the counts describe whatever proof was installed before it, and
//! there are no counts when none was.
//!
//! A proof a component solve installs can rest on rows of another
//! component. For example, with `a > 0`, `b > 0` and
//! `a * b < 0` in the first component and
//! `(= (bvmul l #x00000002) #x00000001)` in the second, the first component's
//! `unsat` hands on a proof resting on the bit-vector row
//! (`executor_tests/partition_rescue.rs` pins that it borrows a row of the
//! second component).
//!
//! [`Executor::published_proof_lenders`] counts the premises of the
//! installed proof: the distinct `assume` terms in the dependency cone of its
//! empty clauses (`ay_proof::empty_clause_cone`, the cone whose `assume`
//! terms `ay_proof::validate_reachable_assumes_in_problem_scope` checks
//! against the problem's assertions). Each premise is attributed
//! by its connecting symbols (`Executor::collect_connecting_symbols`) and the
//! partition's connector table. A premise is
//!
//! - borrowed, when every one of its symbols belongs to a component other
//!   than the one whose `unsat` was returned; the lender is the lowest index
//!   among the components owning a borrowed premise;
//! - unowned, when the table cannot attribute it: the symbol walk declines
//!   its term, it has no symbol, or one of its symbols has no connector (a
//!   symbol preprocessing introduced, for example);
//! - otherwise neither: it has a symbol of the returning component.
//!
//! The counts describe the proof installed when the rescue returns, which
//! publication can still replace.

use std::collections::{HashMap, HashSet};

use ay_core::{Proof, ProofStep, TermId};

use super::Connector;
use crate::executor::Executor;

/// The premise counts of one installed proof (module docs).
#[derive(Debug, PartialEq, Eq)]
pub(super) struct PremiseOwners {
    /// Borrowed premises, each distinct term once.
    pub(super) borrowed_rows: u64,
    /// The lowest index of a component owning a symbol of a borrowed
    /// premise; `None` when no premise is borrowed.
    pub(super) lender: Option<usize>,
    /// Unowned premises, each distinct term once.
    pub(super) unowned_premises: u64,
}

impl Executor {
    /// The premise counts of the installed proof (`last_proof`) when
    /// component `winner` of the partition that `connectors` describe
    /// returned the rescue's `unsat`, or `None` when no proof is installed.
    /// The module docs give the rule that attributes each premise.
    pub(super) fn published_proof_lenders(
        &self,
        winner: usize,
        connectors: &[Connector],
    ) -> Option<PremiseOwners> {
        let proof = self.last_proof.as_ref()?;
        let owner: HashMap<&str, usize> = connectors
            .iter()
            .map(|connector| (connector.name.as_str(), connector.component))
            .collect();
        let mut owners = PremiseOwners {
            borrowed_rows: 0,
            lender: None,
            unowned_premises: 0,
        };
        for premise in reachable_premises(proof) {
            let Some(components) = self.premise_components(premise, &owner) else {
                owners.unowned_premises += 1;
                continue;
            };
            if components.contains(&winner) {
                continue;
            }
            let Some(&lowest) = components.iter().min() else {
                continue;
            };
            owners.borrowed_rows += 1;
            owners.lender = Some(owners.lender.map_or(lowest, |lender| lender.min(lowest)));
        }
        Some(owners)
    }

    /// The components owning the connecting symbols of `premise`, each once,
    /// or `None` when `owner` cannot attribute it (module docs).
    fn premise_components(
        &self,
        premise: TermId,
        owner: &HashMap<&str, usize>,
    ) -> Option<Vec<usize>> {
        let mut names = Vec::new();
        if !self.collect_connecting_symbols(premise, &mut names) || names.is_empty() {
            return None;
        }
        let mut components = Vec::new();
        for name in &names {
            let &component = owner.get(name.as_str())?;
            if !components.contains(&component) {
                components.push(component);
            }
        }
        Some(components)
    }
}

/// The distinct `assume` terms in the dependency cone of `proof`'s empty
/// clauses (`ay_proof::empty_clause_cone`), in step order.
fn reachable_premises(proof: &Proof) -> Vec<TermId> {
    let cone = ay_proof::empty_clause_cone(proof);
    let mut seen = HashSet::new();
    let mut premises = Vec::new();
    for (step, in_cone) in proof.steps.iter().zip(cone) {
        if let ProofStep::Assume(term) = step {
            if in_cone && seen.insert(*term) {
                premises.push(*term);
            }
        }
    }
    premises
}

#[cfg(test)]
#[path = "ownership_tests.rs"]
mod tests;
