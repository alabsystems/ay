// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A bounded, structural projection of native propositional proof steps.
//! Unsupported rules decline; no proof is reconstructed from printed text.
use crate::api::{Solver, Term};
use ay_core::{AletheRule, ProofStep, TermData, TermId};

const MAX_NODES: usize = 65_536;
const MAX_EDGES: usize = 262_144;

/// Native proof applications with an exact Z3 rule correspondence.
#[derive(Clone, Debug)]
pub enum NativeProofApplication {
    /// An input premise of the native derivation or its exact tracking expansion.
    Asserted(Term),
    /// Exact elimination of a tracked assertion's implication guard.
    ModusPonens {
        /// Indices of the asserted label and implication guard.
        premises: [usize; 2],
        /// The implication's consequent.
        conclusion: Term,
    },
    /// A genuine resolution step with one unit premise.
    UnitResolution {
        /// Indices of the resolved proof applications.
        premises: [usize; 2],
        /// Clause produced by the resolution.
        conclusion: Vec<Term>,
    },
}
/// A context-local, immutable native proof DAG. Terms remain authenticated
/// capabilities of the producing Solver; they are never portable raw IDs.
#[derive(Clone, Debug)]
pub struct NativeProofDag {
    /// Proof applications in dependency order.
    pub applications: Vec<NativeProofApplication>,
    /// Index of the application that proves the DAG's conclusion.
    pub root: usize,
}

impl Solver {
    /// Import a supported SMT-LIB proof and its exact unnamed query inputs
    /// structurally into this Solver. Named/tracked premises currently decline:
    /// their implication-and-label expansion needs a separate faithful binding.
    #[doc(hidden)]
    pub fn import_executor_proof_dag(
        &mut self,
        source: &crate::Executor,
    ) -> Option<(NativeProofDag, Vec<Term>)> {
        let count = source
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(MAX_EDGES)?
            .len();
        if source.context().named_terms_iter().next().is_some() {
            return None;
        }
        self.import_executor_proof_dag_with_tracking(
            source,
            &vec![NativeProofInputBinding::Untracked; count],
            &mut NativeProofTrackingCache::default(),
        )
    }

    /// Import exact assertion-time tracked bindings along with the derivation.
    #[doc(hidden)]
    pub fn import_executor_proof_dag_with_tracking(
        &mut self,
        source: &crate::Executor,
        bindings: &[NativeProofInputBinding],
        tracking: &mut NativeProofTrackingCache,
    ) -> Option<(NativeProofDag, Vec<Term>)> {
        let proof = source.last_proof()?;
        if proof.steps.is_empty() || proof.steps.len() > MAX_NODES {
            return None;
        }
        let mut inputs = source
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(MAX_EDGES)?;
        if inputs.len() != bindings.len() {
            return None;
        }
        inputs.extend_from_slice(source.native_proof_query_assumptions()?);
        let authorized = inputs.iter().copied().collect();
        let mut roots = inputs.clone();
        for step in &proof.steps {
            match step {
                ProofStep::Assume(term) => roots.push(*term),
                ProofStep::Resolution { clause, pivot, .. } => {
                    roots.extend_from_slice(clause);
                    roots.push(*pivot);
                }
                ProofStep::Step {
                    rule: AletheRule::False,
                    clause,
                    args,
                    ..
                } if args.is_empty() => roots.extend_from_slice(clause),
                _ => return None,
            }
            if roots.len() > MAX_EDGES {
                return None;
            }
        }
        if roots
            .iter()
            .any(|id| source.terms().entry_stamp(*id).is_none())
        {
            return None;
        }
        let translated = self.translate_native_terms_from(source.terms(), &roots);
        let mapped: std::collections::HashMap<_, _> =
            roots.into_iter().zip(translated.iter().copied()).collect();
        let dag = project_native_proof(source.terms(), proof, &authorized, |id| {
            mapped.get(&id).copied()
        })?;
        self.bind_native_tracking(dag, &translated[..inputs.len()], bindings, tracking)
    }

    /// Project supported steps from this query's actual retained proof.
    /// The projection is all-or-nothing, bounded, and never changes a verdict.
    #[doc(hidden)]
    pub fn native_proof_dag(
        &self,
        input_assertions: impl IntoIterator<Item = Term>,
    ) -> Option<NativeProofDag> {
        let proof = self.executor.last_proof()?;
        if proof.steps.is_empty() || proof.steps.len() > MAX_NODES {
            return None;
        }
        let mut authorized = ay_core::kani_compat::DetHashSet::default();
        for (count, assertion) in input_assertions.into_iter().enumerate() {
            if count >= MAX_EDGES {
                return None;
            }
            authorized.insert(self.resolve_term("native_proof_dag", assertion).ok()?);
        }
        project_native_proof(self.terms(), proof, &authorized, |id| {
            self.terms().entry_stamp(id).map(|_| self.wrap_term(id))
        })
    }
}

#[path = "dag_tracking.rs"]
mod tracking;
pub use tracking::{NativeProofInputBinding, NativeProofTrackingCache};

fn project_native_proof(
    terms: &ay_core::TermStore,
    proof: &ay_core::Proof,
    authorized: &ay_core::kani_compat::DetHashSet<TermId>,
    wrap: impl Fn(TermId) -> Option<Term>,
) -> Option<NativeProofDag> {
    // The checked native exact-false derivation resolves its actual false
    // premise with Alethe's `(not false)` axiom. Both native conclusions
    // denote false; Z3 represents this proof by that same asserted node.
    if let [ProofStep::Assume(term), ProofStep::Step {
        rule: AletheRule::False,
        clause,
        premises,
        args,
    }, ProofStep::Resolution {
        clause: result,
        pivot,
        clause1,
        clause2,
    }] = proof.steps.as_slice()
    {
        if terms.entry_stamp(*term).is_some()
            && terms.is_false(*term)
            && clause.len() == 1
            && terms.entry_stamp(clause[0]).is_some()
            && matches!(terms.get(clause[0]), TermData::Not(child) if child == term)
            && premises.is_empty()
            && args.is_empty()
            && result.is_empty()
            && pivot == term
            && clause1.0 == 0
            && clause2.0 == 1
            && authorized.contains(term)
        {
            return Some(NativeProofDag {
                applications: vec![NativeProofApplication::Asserted(wrap(*term)?)],
                root: 0,
            });
        }
    }
    let mut applications = Vec::new();
    let mut indices = Vec::new();
    let mut clauses = Vec::<Vec<TermId>>::new();
    let mut edges = 0usize;
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => {
                if !authorized.contains(term) {
                    return None;
                }
                let value = wrap(*term)?;
                let clause = if terms.is_false(*term) {
                    Vec::new()
                } else {
                    // Keep the asserted formula intact. Splitting a named
                    // application by spelling alone could reinterpret a UF.
                    vec![*term]
                };
                edges = edges.checked_add(clause.len())?;
                if edges > MAX_EDGES {
                    return None;
                }
                indices.push(applications.len());
                applications.push(NativeProofApplication::Asserted(value));
                clauses.push(clause);
            }
            ProofStep::Resolution {
                clause,
                clause1,
                clause2,
                ..
            } => {
                let (first, second) = (clause1.0 as usize, clause2.0 as usize);
                let left = clauses.get(first)?;
                let right = clauses.get(second)?;
                let (base, unit, base_id, unit_id) = if right.len() == 1 {
                    (left, right[0], first, second)
                } else if left.len() == 1 {
                    (right, left[0], second, first)
                } else {
                    return None;
                };
                let opposite = |other: TermId| {
                    matches!(terms.get(other), TermData::Not(child) if *child == unit)
                        || matches!(terms.get(unit), TermData::Not(child) if *child == other)
                };
                if !base.iter().any(|term| opposite(*term)) {
                    return None;
                }
                let result = base
                    .iter()
                    .copied()
                    .filter(|term| !opposite(*term))
                    .collect::<Vec<_>>();
                if result != *clause {
                    return None;
                }
                edges = edges.checked_add(clause.len().checked_add(2)?)?;
                if edges > MAX_EDGES {
                    return None;
                }
                let conclusion = clause
                    .iter()
                    .copied()
                    .map(&wrap)
                    .collect::<Option<Vec<_>>>()?;
                let premises = [*indices.get(base_id)?, *indices.get(unit_id)?];
                indices.push(applications.len());
                applications.push(NativeProofApplication::UnitResolution {
                    premises,
                    conclusion,
                });
                clauses.push(clause.clone());
            }
            _ => return None,
        }
    }
    if !clauses.last()?.is_empty() {
        return None;
    }
    Some(NativeProofDag {
        applications,
        root: *indices.last()?,
    })
}
