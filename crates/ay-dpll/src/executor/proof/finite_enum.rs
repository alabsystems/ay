// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, query-sealed proof path for direct finite-enum pigeonholes.

use ay_core::term::TermEntryStamp;
use ay_core::{AletheRule, Proof, ProofStep, Sort, Symbol, TermData, TermId};
use ay_frontend::SourceContextStamp;

use crate::executor::{Executor, QueryAuthorityEpoch};

use super::finite_enum_surface::FiniteEnumProofSurface;

const MAX_MEMBERS: usize = 256;
const MAX_PAIRS: usize = 32_640;
const MAX_DIRECT_ROOT_SCAN: usize = 1_048_576;
const MAX_DECLARATION_SCAN: usize = 4_096;
pub(super) const MAX_PROOF_CELLS: usize = 131_072;
const MAX_REGISTRY_STRING_BYTES: usize = 8 * 1024 * 1024;
const MAX_CHECK_WORK: usize = 250_000_000;
const MAX_CHECK_BYTES: usize = 512 * 1024 * 1024;
const MAX_BUNDLE_TERM_BYTES: usize = 256 * 1024 * 1024;
pub(super) const MAX_RENDER_WORK: u64 = 64 * 1024 * 1024;

#[derive(Debug)]
struct CheckedSource {
    root_index: usize,
    term: TermId,
    entry: TermEntryStamp,
}

/// Authority for one exact canonical proof and one immutable public query.
#[derive(Debug)]
pub(in crate::executor) struct CheckedFiniteEnumPigeonholeProof {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    root_len: usize,
    members: Box<[TermId]>,
    member_entries: Box<[TermEntryStamp]>,
    sources: Box<[CheckedSource]>,
    equalities: Box<[TermId]>,
    equality_entries: Box<[TermEntryStamp]>,
    pub(super) surface: Option<FiniteEnumProofSurface>,
    pub(super) datatype_decls: Box<[(String, Vec<String>)]>,
    pub(super) selector_decls: Box<[(String, Vec<String>)]>,
    pub(super) member_signatures: Box<[ay_proof::DatatypeMemberSignature]>,
}

impl CheckedFiniteEnumPigeonholeProof {
    pub(super) fn assumptions(&self) -> impl ExactSizeIterator<Item = TermId> + '_ {
        self.sources.iter().map(|source| source.term)
    }

    fn matches_proof(&self, proof: &Proof) -> bool {
        let edges = self.sources.len();
        let Some(ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind,
            lia,
        }) = proof.steps.first()
        else {
            return false;
        };
        if proof.steps.len() != edges.saturating_add(2)
            || !proof.named_steps.is_empty()
            || theory != "DT"
            || clause.as_slice() != self.equalities.as_ref()
            || farkas.is_some()
            || *kind != ay_core::TheoryLemmaKind::DatatypeEnumPigeonhole
            || lia.is_some()
            || !proof.steps[1..=edges]
                .iter()
                .zip(self.assumptions())
                .all(|(step, term)| matches!(step, ProofStep::Assume(found) if *found == term))
        {
            return false;
        }
        matches!(
            proof.steps.last(),
            Some(ProofStep::Step {
                rule: AletheRule::Resolution,
                clause,
                premises,
                args,
            }) if clause.is_empty()
                && args.is_empty()
                && premises.len() == edges + 1
                && premises.iter().enumerate().all(|(index, premise)| {
                    usize::try_from(premise.0).ok() == Some(index)
                })
        )
    }

    fn is_current_for(&self, executor: &Executor, proof: &Proof) -> bool {
        if !self.matches_proof(proof) {
            return false;
        }
        let Some((epoch, source_stamp, roots)) =
            executor.bounded_plain_unsat_query_scope(MAX_DIRECT_ROOT_SCAN)
        else {
            return false;
        };
        self.query_epoch.is_same_epoch(&epoch)
            && self.source_context_stamp == source_stamp
            && roots.len() == self.root_len
            && self.members.len() == self.member_entries.len()
            && self.equalities.len() == self.equality_entries.len()
            && self.sources.iter().all(|source| {
                roots.get(source.root_index) == Some(&source.term)
                    && executor.ctx.terms.entry_stamp(source.term) == Some(source.entry)
            })
            && self
                .members
                .iter()
                .copied()
                .zip(self.member_entries.iter().copied())
                .all(|(term, entry)| executor.ctx.terms.entry_stamp(term) == Some(entry))
            && self
                .equalities
                .iter()
                .copied()
                .zip(self.equality_entries.iter().copied())
                .all(|(term, entry)| executor.ctx.terms.entry_stamp(term) == Some(entry))
            && executor
                .proof_problem_assertion_provenance
                .as_ref()
                .is_some_and(|provenance| {
                    provenance.original_problem_assertions.as_slice() == roots
                })
    }
}

#[cfg(test)]
impl Executor {
    pub(in crate::executor) fn plant_stale_finite_enum_sidecars_for_test(&mut self) {
        self.last_finite_enum_pigeonhole = Some(crate::executor::FiniteEnumPigeonholeWitness {
            k: 0,
            members: Vec::new(),
            edge_sources: Default::default(),
        });
        self.last_checked_finite_enum_pigeonhole = Some(CheckedFiniteEnumPigeonholeProof {
            query_epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            root_len: self.ctx.assertions.len(),
            members: Box::new([]),
            member_entries: Box::new([]),
            sources: Box::new([]),
            equalities: Box::new([]),
            equality_entries: Box::new([]),
            surface: None,
            datatype_decls: Box::new([]),
            selector_decls: Box::new([]),
            member_signatures: Box::new([]),
        });
    }
}

impl Executor {
    pub(super) fn bounded_pair_count(k: usize, members: usize) -> Option<usize> {
        if k == 0 || members > MAX_MEMBERS || members != k.checked_add(1)? {
            return None;
        }
        let pairs = members.checked_mul(members.checked_sub(1)?)? / 2;
        (pairs <= MAX_PAIRS).then_some(pairs)
    }

    pub(super) fn checked_finite_enum_capability_for_proof(
        &self,
        proof: &Proof,
    ) -> Option<&CheckedFiniteEnumPigeonholeProof> {
        let capability = self.last_checked_finite_enum_pigeonhole.as_ref()?;
        let stored = self.last_proof.as_ref()?;
        capability
            .is_current_for(self, stored)
            .then_some(capability)
            .filter(|capability| capability.matches_proof(proof))
    }

    pub(super) fn current_checked_finite_enum_proof(
        &self,
    ) -> Option<&CheckedFiniteEnumPigeonholeProof> {
        self.checked_finite_enum_capability_for_proof(self.last_proof.as_ref()?)
    }

    pub(crate) fn last_proof_is_checked_finite_enum(&self) -> bool {
        self.current_checked_finite_enum_proof().is_some()
    }

    pub(in crate::executor) fn finite_enum_scope_for_proof(
        &self,
        proof: &Proof,
    ) -> Option<Vec<TermId>> {
        Some(
            self.checked_finite_enum_capability_for_proof(proof)?
                .assumptions()
                .collect(),
        )
    }

    pub(crate) fn checked_finite_enum_export_declarations(
        &self,
        proof: &Proof,
    ) -> Option<(
        Vec<(String, Vec<String>)>,
        Vec<(String, Vec<String>)>,
        Vec<ay_proof::DatatypeMemberSignature>,
    )> {
        let capability = self.checked_finite_enum_capability_for_proof(proof)?;
        Some((
            capability.datatype_decls.to_vec(),
            capability.selector_decls.to_vec(),
            capability.member_signatures.to_vec(),
        ))
    }

    pub(crate) fn checked_finite_enum_bundle_export_is_bounded(&self, proof: &Proof) -> bool {
        self.checked_finite_enum_capability_for_proof(proof)
            .is_some_and(|_| {
                self.ctx.terms.instance_term_bytes() <= MAX_BUNDLE_TERM_BYTES
                    && self.ctx.terms.true_memory_bytes() <= MAX_BUNDLE_TERM_BYTES
            })
    }

    pub(super) fn check_bounded_finite_enum_proof(
        &self,
        proof: &Proof,
        assumptions: &[TermId],
        datatype_decls: &[(String, Vec<String>)],
        selector_decls: &[(String, Vec<String>)],
        member_signatures: &[ay_proof::DatatypeMemberSignature],
    ) -> Result<ay_proof::ProofQuality, ay_proof::ProofCheckError> {
        let (mut work, mut bytes) = (0usize, 0usize);
        let mut progress = |work_delta: usize, byte_delta: usize| {
            let Some(next_work) = work.checked_add(work_delta) else {
                return false;
            };
            let Some(next_bytes) = bytes.checked_add(byte_delta) else {
                return false;
            };
            work = next_work;
            bytes = next_bytes;
            work <= MAX_CHECK_WORK && bytes <= MAX_CHECK_BYTES
        };
        ay_proof::check_proof_strict_with_typed_context_and_progress(
            proof,
            &self.ctx.terms,
            Some(datatype_decls),
            Some(selector_decls),
            member_signatures,
            Some(assumptions),
            &mut progress,
        )
    }

    pub(super) fn try_install_bounded_finite_enum_pigeonhole_proof(&mut self) -> bool {
        let Some(witness) = self.last_finite_enum_pigeonhole.as_ref() else {
            return false;
        };
        let Some(pairs) = Self::bounded_pair_count(witness.k, witness.members.len()) else {
            return false;
        };
        if witness.edge_sources.len() != pairs
            || pairs
                .checked_mul(4)
                .and_then(|cells| cells.checked_add(3))
                .is_none_or(|cells| cells > MAX_PROOF_CELLS)
        {
            return false;
        }
        // The detector may retain millions of edges. Copy only after both the
        // member and exact edge-count bounds have succeeded.
        let witness = witness.clone();

        let Some((query_epoch, source_context_stamp, roots)) =
            self.bounded_plain_unsat_query_scope(MAX_DIRECT_ROOT_SCAN)
        else {
            return false;
        };
        if self
            .proof_problem_assertion_provenance
            .as_ref()
            .is_none_or(|provenance| provenance.original_problem_assertions.as_slice() != roots)
        {
            return false;
        }
        let mut seen_members = ay_core::kani_compat::DetHashSet::default();
        if !witness
            .members
            .iter()
            .copied()
            .all(|member| seen_members.insert(member))
        {
            return false;
        }
        let Some(&first_member) = witness.members.first() else {
            return false;
        };
        let Sort::Uninterpreted(sort_name) = self.ctx.terms.sort(first_member) else {
            return false;
        };
        if sort_name.len() > MAX_REGISTRY_STRING_BYTES
            || !witness.members.iter().all(|&member| {
                matches!(self.ctx.terms.sort(member), Sort::Uninterpreted(name) if name == sort_name)
            })
        {
            return false;
        }
        let sort_name = sort_name.clone();

        let (mut assumptions, mut equalities) = (Vec::new(), Vec::new());
        if assumptions.try_reserve_exact(pairs).is_err()
            || equalities.try_reserve_exact(pairs).is_err()
        {
            return false;
        }
        let mut seen_sources = ay_core::kani_compat::DetHashSet::default();
        for (index, &left) in witness.members.iter().enumerate() {
            for &right in &witness.members[index + 1..] {
                let key = if left.0 < right.0 {
                    (left, right)
                } else {
                    (right, left)
                };
                let Some(&source) = witness.edge_sources.get(&key) else {
                    return false;
                };
                let TermData::Not(equality) = self.ctx.terms.get(source) else {
                    return false;
                };
                let equality = *equality;
                let TermData::App(Symbol::Named(symbol), args) = self.ctx.terms.get(equality)
                else {
                    return false;
                };
                if symbol != "="
                    || args.as_slice() != [left, right] && args.as_slice() != [right, left]
                    || !seen_sources.insert(source)
                    || self.ctx.terms.entry_stamp(source).is_none()
                    || self.ctx.terms.entry_stamp(equality).is_none()
                {
                    return false;
                }
                assumptions.push(source);
                equalities.push(equality);
            }
        }
        if assumptions.len() != pairs || equalities.len() != pairs {
            return false;
        }

        let needed: ay_core::kani_compat::DetHashSet<TermId> =
            assumptions.iter().copied().collect();
        let mut root_indices = ay_core::kani_compat::DetHashMap::default();
        for (index, &root) in roots.iter().enumerate() {
            if needed.contains(&root) {
                root_indices.entry(root).or_insert(index);
            }
        }
        if root_indices.len() != pairs {
            return false;
        }
        let Some(sources) = assumptions
            .iter()
            .map(|&term| {
                Some(CheckedSource {
                    root_index: *root_indices.get(&term)?,
                    term,
                    entry: self.ctx.terms.entry_stamp(term)?,
                })
            })
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        let Some(member_entries) = witness
            .members
            .iter()
            .map(|&term| self.ctx.terms.entry_stamp(term))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        let Some(equality_entries) = equalities
            .iter()
            .map(|&term| self.ctx.terms.entry_stamp(term))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        // Surface syntax is presentation authority only. Its absence must not
        // weaken or suppress the independently strict-checked internal proof.
        let surface_sources: Vec<(usize, TermId)> = sources
            .iter()
            .map(|source| (source.root_index, source.term))
            .collect();
        let surface = self.build_finite_enum_proof_surface(
            roots,
            &surface_sources,
            &equalities,
            &witness.members,
        );

        let mut constructors = None;
        for (index, (name, candidate)) in self.ctx.datatype_iter().enumerate() {
            if index >= MAX_DECLARATION_SCAN {
                return false;
            }
            if name == sort_name {
                constructors = Some(candidate);
                break;
            }
        }
        let Some(constructors) = constructors else {
            return false;
        };
        if constructors.len() != witness.k {
            return false;
        }
        let mut registry_bytes = sort_name.len().checked_mul(2);
        for constructor in constructors {
            registry_bytes = registry_bytes.and_then(|bytes| {
                constructor
                    .len()
                    .checked_mul(4)
                    .and_then(|extra| bytes.checked_add(extra))
            });
        }
        if registry_bytes.is_none_or(|bytes| bytes > MAX_REGISTRY_STRING_BYTES) {
            return false;
        }
        let constructors = constructors.to_vec();
        let names: ay_core::kani_compat::DetHashSet<String> =
            constructors.iter().cloned().collect();
        let mut selectors_by_constructor = ay_core::kani_compat::DetHashMap::default();
        for (index, (constructor, selectors)) in self.ctx.ctor_selectors_iter().enumerate() {
            if index >= MAX_DECLARATION_SCAN {
                return false;
            }
            if !names.contains(constructor) {
                continue;
            }
            let mut next_bytes =
                registry_bytes.and_then(|bytes| bytes.checked_add(constructor.len()));
            for selector in selectors {
                next_bytes = next_bytes.and_then(|bytes| bytes.checked_add(selector.len()));
            }
            if next_bytes.is_none_or(|bytes| bytes > MAX_REGISTRY_STRING_BYTES)
                || selectors_by_constructor
                    .insert(constructor.clone(), selectors.clone())
                    .is_some()
            {
                return false;
            }
            registry_bytes = next_bytes;
        }
        let mut selector_decls = Vec::new();
        if selector_decls
            .try_reserve_exact(constructors.len())
            .is_err()
        {
            return false;
        }
        for constructor in &constructors {
            let Some(selectors) = selectors_by_constructor.remove(constructor) else {
                return false;
            };
            if !selectors.is_empty() {
                return false;
            }
            selector_decls.push((constructor.clone(), selectors));
        }
        let datatype_decls = vec![(sort_name, constructors)];
        let mut member_signatures = Vec::new();
        for constructor in &datatype_decls[0].1 {
            let tester = format!("is-{constructor}");
            for identity in [constructor.as_str(), tester.as_str()] {
                let Some(info) = self.ctx.exact_datatype_member_info(identity) else {
                    return false;
                };
                member_signatures.push(ay_proof::DatatypeMemberSignature {
                    identity: identity.to_string(),
                    argument_sorts: info.arg_sorts.clone(),
                    result_sort: info.sort.clone(),
                    nullary_term: info.term,
                });
            }
        }

        let mut proof = Proof::new();
        let mut premises = Vec::new();
        if premises.try_reserve_exact(pairs + 1).is_err() {
            return false;
        }
        premises.push(proof.add_theory_lemma_with_kind(
            "DT",
            equalities.clone(),
            ay_core::TheoryLemmaKind::DatatypeEnumPigeonhole,
        ));
        for &assumption in &assumptions {
            premises.push(proof.add_assume(assumption, None));
        }
        proof.add_rule_step(AletheRule::Resolution, Vec::new(), premises, Vec::new());
        let Ok(quality) = self.check_bounded_finite_enum_proof(
            &proof,
            &assumptions,
            &datatype_decls,
            &selector_decls,
            &member_signatures,
        ) else {
            return false;
        };
        let capability = CheckedFiniteEnumPigeonholeProof {
            query_epoch,
            source_context_stamp,
            root_len: roots.len(),
            members: witness.members.into_boxed_slice(),
            member_entries: member_entries.into_boxed_slice(),
            sources: sources.into_boxed_slice(),
            equalities: equalities.into_boxed_slice(),
            equality_entries: equality_entries.into_boxed_slice(),
            surface,
            datatype_decls: datatype_decls.into_boxed_slice(),
            selector_decls: selector_decls.into_boxed_slice(),
            member_signatures: member_signatures.into_boxed_slice(),
        };
        if !capability.matches_proof(&proof) {
            return false;
        }
        let total = u32::try_from(proof.steps.len()).unwrap_or(u32::MAX);
        self.last_proof_term_overrides = None;
        self.last_lrat_certificate = None;
        self.proof_check_result = Some(ay_proof::PartialProofCheck {
            checked_steps: total,
            skipped_hole_steps: 0,
            total_steps: total,
        });
        self.proof_check_ok = true;
        self.populate_proof_quality_stats(&quality);
        self.last_proof_quality = Some(quality);
        self.last_proof = Some(proof);
        self.last_checked_finite_enum_pigeonhole = Some(capability);
        self.last_finite_enum_pigeonhole = None;
        true
    }
}
