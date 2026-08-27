// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation accounting for coherent proof-tracker rollback snapshots.

use std::mem::size_of;

use ay_core::{AletheRule, LiaAnnotation, ProofId, ProofStep, Sort, TermId};

use super::lemma_dedup::{LemmaBucket, LemmaDedupMap, LemmaKey};
use super::{HashMap, ProofTracker, ProofTrackerCheckpoint};

const MIN_CHECKPOINT_CHARGE_BYTES: usize = 4 * 1024;
const ALLOCATION_OVERHEAD_BYTES: usize = 64;
const MAP_SLOT_OVERHEAD_BYTES: usize = 64;
const MAX_ACCOUNTED_SORT_DEPTH: usize = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckpointCloneError {
    LimitExceeded,
    UnsupportedPayload,
}

impl ProofTracker {
    fn checkpoint_clone_bytes(&self, limit: usize) -> Result<usize, CheckpointCloneError> {
        let mut footprint = Footprint::new(limit)?;
        footprint.allocation::<ProofStep>(self.proof.steps.len())?;
        for step in &self.proof.steps {
            proof_step_payload(&mut footprint, step)?;
        }
        map_storage(&mut footprint, &self.assumption_map)?;
        lemma_dedup_map(&mut footprint, &self.lemma_map)?;
        named_map(&mut footprint, &self.proof.named_steps)?;
        footprint.allocation::<usize>(self.scope_stack.len())?;
        footprint.allocation::<HashMap<TermId, ProofId>>(self.scope_assumption_maps.len())?;
        for map in &self.scope_assumption_maps {
            map_storage(&mut footprint, map)?;
        }
        footprint.allocation::<LemmaDedupMap>(self.scope_lemma_maps.len())?;
        for map in &self.scope_lemma_maps {
            lemma_dedup_map(&mut footprint, map)?;
        }
        footprint.allocation::<HashMap<String, ProofId>>(self.scope_named_steps.len())?;
        for map in &self.scope_named_steps {
            named_map(&mut footprint, map)?;
        }
        footprint.string(&self.theory_name)?;
        let charge = footprint.bytes.max(MIN_CHECKPOINT_CHARGE_BYTES);
        if charge > limit {
            return Err(CheckpointCloneError::LimitExceeded);
        }
        Ok(charge)
    }

    #[cfg(test)]
    pub(crate) fn checkpoint_clone_charge_for_test(&self) -> Result<usize, CheckpointCloneError> {
        self.checkpoint_clone_bytes(usize::MAX)
    }

    /// Capture a coherent proof-ledger snapshot for speculative work.
    ///
    /// The caller owns the cumulative query meter. This method performs one
    /// early-bounded conservative footprint walk, then clones only when every
    /// owning payload plus fixed allocation surcharges fits `max_charge`.
    #[must_use = "a bounded rollback checkpoint must be consumed or deliberately discarded"]
    pub(crate) fn rollback_checkpoint_bounded(
        &self,
        max_charge: usize,
    ) -> Result<(ProofTrackerCheckpoint, usize), CheckpointCloneError> {
        let charge = self.checkpoint_clone_bytes(max_charge)?;
        Ok((
            ProofTrackerCheckpoint {
                steps: self.proof.steps.clone(),
                ledger_identity: self.ledger_identity.clone(),
                ledger_epoch: self.ledger_epoch,
                assumption_map: self.assumption_map.clone(),
                lemma_map: self.lemma_map.clone(),
                named_steps: self.proof.named_steps.clone(),
                scope_stack: self.scope_stack.clone(),
                scope_assumption_maps: self.scope_assumption_maps.clone(),
                scope_lemma_maps: self.scope_lemma_maps.clone(),
                scope_named_steps: self.scope_named_steps.clone(),
                enabled: self.enabled,
                theory_name: self.theory_name.clone(),
            },
            charge,
        ))
    }

    #[cfg(test)]
    pub(crate) fn rollback_checkpoint(&self) -> Option<ProofTrackerCheckpoint> {
        self.rollback_checkpoint_bounded(usize::MAX)
            .ok()
            .map(|(checkpoint, _)| checkpoint)
    }

    /// Consume a snapshot to restore only non-positional tracker metadata.
    pub(crate) fn restore_checkpoint_metadata(&mut self, checkpoint: ProofTrackerCheckpoint) {
        self.enabled = checkpoint.enabled;
        self.theory_name = checkpoint.theory_name;
    }

    /// Discard every proof artifact added after `checkpoint`.
    ///
    /// Returns `true` when the original ledger was still present and its exact
    /// prefix was restored. If the ledger was moved, clears the replacement
    /// ledger and returns `false` so paired term rollback can retain its terms.
    #[must_use]
    pub(crate) fn rollback_to(&mut self, checkpoint: ProofTrackerCheckpoint) -> bool {
        let ProofTrackerCheckpoint {
            steps,
            ledger_identity,
            ledger_epoch,
            assumption_map,
            lemma_map,
            named_steps,
            mut scope_stack,
            mut scope_assumption_maps,
            mut scope_lemma_maps,
            mut scope_named_steps,
            enabled,
            theory_name,
        } = checkpoint;
        let same_ledger = std::sync::Arc::ptr_eq(&ledger_identity, &self.ledger_identity)
            && ledger_epoch == self.ledger_epoch;
        if same_ledger {
            self.proof.steps = steps;
            self.assumption_map = assumption_map;
            self.lemma_map = lemma_map;
            self.proof.named_steps = named_steps;
            self.scope_stack = scope_stack;
            self.scope_assumption_maps = scope_assumption_maps;
            self.scope_lemma_maps = scope_lemma_maps;
            self.scope_named_steps = scope_named_steps;
        } else {
            self.proof.steps = Vec::new();
            self.assumption_map = HashMap::default();
            self.lemma_map = LemmaDedupMap::default();
            self.proof.named_steps = HashMap::default();
            scope_stack.fill(0);
            for map in &mut scope_assumption_maps {
                *map = HashMap::default();
            }
            for map in &mut scope_lemma_maps {
                *map = LemmaDedupMap::default();
            }
            for map in &mut scope_named_steps {
                *map = HashMap::default();
            }
            self.scope_stack = scope_stack;
            self.scope_assumption_maps = scope_assumption_maps;
            self.scope_lemma_maps = scope_lemma_maps;
            self.scope_named_steps = scope_named_steps;
            self.advance_ledger_epoch();
        }
        self.enabled = enabled;
        self.theory_name = theory_name;
        same_ledger
    }
}

struct Footprint {
    bytes: usize,
    limit: usize,
}

impl Footprint {
    fn new(limit: usize) -> Result<Self, CheckpointCloneError> {
        let bytes = size_of::<ProofTrackerCheckpoint>();
        if bytes > limit {
            return Err(CheckpointCloneError::LimitExceeded);
        }
        Ok(Self { bytes, limit })
    }

    fn charge(&mut self, amount: usize) -> Result<(), CheckpointCloneError> {
        let next = self
            .bytes
            .checked_add(amount)
            .ok_or(CheckpointCloneError::UnsupportedPayload)?;
        if next > self.limit {
            return Err(CheckpointCloneError::LimitExceeded);
        }
        self.bytes = next;
        Ok(())
    }

    fn allocation<T>(&mut self, len: usize) -> Result<(), CheckpointCloneError> {
        let allocation_overhead = if len != 0 {
            ALLOCATION_OVERHEAD_BYTES
        } else {
            0
        };
        let bytes = len
            .checked_mul(size_of::<T>())
            .and_then(|bytes| bytes.checked_add(allocation_overhead))
            .ok_or(CheckpointCloneError::UnsupportedPayload)?;
        self.charge(bytes)
    }

    fn string(&mut self, value: &str) -> Result<(), CheckpointCloneError> {
        let allocation_overhead = if value.is_empty() {
            0
        } else {
            ALLOCATION_OVERHEAD_BYTES
        };
        let bytes = value
            .len()
            .checked_add(allocation_overhead)
            .ok_or(CheckpointCloneError::UnsupportedPayload)?;
        self.charge(bytes)
    }
}

fn map_storage<K, V>(
    footprint: &mut Footprint,
    map: &HashMap<K, V>,
) -> Result<(), CheckpointCloneError> {
    let slots = map_slots(map);
    let slot_bytes = size_of::<(K, V)>()
        .checked_add(MAP_SLOT_OVERHEAD_BYTES)
        .ok_or(CheckpointCloneError::UnsupportedPayload)?;
    let allocation_overhead = if slots != 0 {
        ALLOCATION_OVERHEAD_BYTES
    } else {
        0
    };
    let bytes = slots
        .checked_mul(slot_bytes)
        .and_then(|bytes| bytes.checked_add(allocation_overhead))
        .ok_or(CheckpointCloneError::UnsupportedPayload)?;
    footprint.charge(bytes)
}

#[cfg(kani)]
fn map_slots<K, V>(map: &HashMap<K, V>) -> usize {
    map.len()
}

#[cfg(not(kani))]
fn map_slots<K, V>(map: &HashMap<K, V>) -> usize {
    // hashbrown's `capacity` determines the clean table's bucket allocation,
    // but deletions can leave tombstones and make it understate that storage.
    // The checkpointed proof maps therefore grow by insertion and are only
    // cleared or replaced; the source-census regression test must be updated
    // before adding remove/retain-style mutation to those maps.
    map.capacity()
}

fn lemma_dedup_map(
    footprint: &mut Footprint,
    map: &LemmaDedupMap,
) -> Result<(), CheckpointCloneError> {
    map_storage(footprint, &map.buckets)?;
    for bucket in map.buckets.values() {
        // Singletons live inline in the outer map. Collisions conservatively
        // charge the bucket's full reserved capacity before key payload walks.
        if let LemmaBucket::Many(entries) = bucket {
            footprint.allocation::<(LemmaKey, ProofId)>(entries.capacity())?;
        }
        for (key, _) in bucket.iter() {
            footprint.allocation::<TermId>(key.clause.capacity())?;
            if let Some(farkas) = &key.farkas {
                footprint.allocation::<(i64, i64)>(farkas.capacity())?;
            }
        }
    }
    Ok(())
}

fn named_map(
    footprint: &mut Footprint,
    map: &HashMap<String, ProofId>,
) -> Result<(), CheckpointCloneError> {
    map_storage(footprint, map)?;
    for name in map.keys() {
        footprint.string(name)?;
    }
    Ok(())
}

fn proof_step_payload(
    footprint: &mut Footprint,
    step: &ProofStep,
) -> Result<(), CheckpointCloneError> {
    match step {
        ProofStep::Assume(_) => {}
        ProofStep::Resolution {
            clause,
            pivot: _,
            clause1: _,
            clause2: _,
        } => footprint.allocation::<TermId>(clause.len())?,
        ProofStep::TheoryLemma {
            theory,
            clause,
            farkas,
            kind: _,
            lia,
        } => {
            footprint.string(theory)?;
            footprint.allocation::<TermId>(clause.len())?;
            if let Some(farkas) = farkas {
                footprint.allocation::<num_rational::Rational64>(farkas.coefficients.len())?;
            }
            match lia {
                Some(LiaAnnotation::CuttingPlane(cut)) => footprint
                    .allocation::<num_rational::Rational64>(cut.farkas.coefficients.len())?,
                Some(
                    LiaAnnotation::BoundsGap
                    | LiaAnnotation::Divisibility
                    | LiaAnnotation::LinearIdentity,
                )
                | None => {}
                Some(_) => return Err(CheckpointCloneError::UnsupportedPayload),
            }
        }
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => {
            alethe_rule_payload(footprint, rule)?;
            footprint.allocation::<TermId>(clause.len())?;
            footprint.allocation::<ProofId>(premises.len())?;
            footprint.allocation::<TermId>(args.len())?;
        }
        ProofStep::Anchor {
            end_step: _,
            variables,
        } => {
            footprint.allocation::<(String, Sort)>(variables.len())?;
            for (name, sort) in variables {
                footprint.string(name)?;
                sort_payload(footprint, sort, 0)?;
            }
        }
        _ => return Err(CheckpointCloneError::UnsupportedPayload),
    }
    Ok(())
}

fn alethe_rule_payload(
    footprint: &mut Footprint,
    rule: &AletheRule,
) -> Result<(), CheckpointCloneError> {
    match rule {
        AletheRule::Custom(name) => footprint.string(name)?,
        AletheRule::True
        | AletheRule::False
        | AletheRule::NotTrue
        | AletheRule::NotFalse
        | AletheRule::And
        | AletheRule::AndPos(_)
        | AletheRule::AndNeg
        | AletheRule::NotAnd
        | AletheRule::Or
        | AletheRule::OrPos(_)
        | AletheRule::OrNeg
        | AletheRule::NotOr
        | AletheRule::Implies
        | AletheRule::ImpliesNeg1
        | AletheRule::ImpliesNeg2
        | AletheRule::NotImplies1
        | AletheRule::NotImplies2
        | AletheRule::Equiv
        | AletheRule::EquivPos1
        | AletheRule::EquivPos2
        | AletheRule::EquivNeg1
        | AletheRule::EquivNeg2
        | AletheRule::NotEquiv1
        | AletheRule::NotEquiv2
        | AletheRule::Ite
        | AletheRule::ItePos1
        | AletheRule::ItePos2
        | AletheRule::IteNeg1
        | AletheRule::IteNeg2
        | AletheRule::NotIte1
        | AletheRule::NotIte2
        | AletheRule::Ite1
        | AletheRule::Ite2
        | AletheRule::IteIntro
        | AletheRule::XorPos1
        | AletheRule::XorPos2
        | AletheRule::XorNeg1
        | AletheRule::XorNeg2
        | AletheRule::ImpliesPos
        | AletheRule::Resolution
        | AletheRule::ThResolution
        | AletheRule::Contraction
        | AletheRule::Weakening
        | AletheRule::Reordering
        | AletheRule::Refl
        | AletheRule::Symm
        | AletheRule::Trans
        | AletheRule::Cong
        | AletheRule::EqReflexive
        | AletheRule::EqSymmetric
        | AletheRule::EqTransitive
        | AletheRule::EqCongruent
        | AletheRule::EqCongruentPred
        | AletheRule::DistinctElim
        | AletheRule::LaTautology
        | AletheRule::LaGeneric
        | AletheRule::LaDisequality
        | AletheRule::LaTotality
        | AletheRule::LaMultPos
        | AletheRule::LaMultNeg
        | AletheRule::LiaGeneric
        | AletheRule::ForallInst
        | AletheRule::Skolem
        | AletheRule::Subproof
        | AletheRule::Bind
        | AletheRule::AllSimplify
        | AletheRule::BoolSimplify
        | AletheRule::ArithSimplify
        | AletheRule::BvBitblast
        | AletheRule::ReadOverWritePos
        | AletheRule::ReadOverWriteNeg
        | AletheRule::StorePermutation
        | AletheRule::ReadOverWriteChain
        | AletheRule::Extensionality
        | AletheRule::ArrayExtDiffIntro
        | AletheRule::FpToBv
        | AletheRule::StringLength
        | AletheRule::StringDecompose
        | AletheRule::StringCodeInj
        | AletheRule::Hole
        | AletheRule::Drup
        | AletheRule::Trust
        | AletheRule::Evaluate
        | AletheRule::QntNegExists => {}
        _ => return Err(CheckpointCloneError::UnsupportedPayload),
    }
    Ok(())
}

fn sort_payload(
    footprint: &mut Footprint,
    sort: &Sort,
    depth: usize,
) -> Result<(), CheckpointCloneError> {
    if depth > MAX_ACCOUNTED_SORT_DEPTH {
        return Err(CheckpointCloneError::UnsupportedPayload);
    }
    match sort {
        Sort::Array(array) => {
            footprint.allocation::<ay_core::ArraySort>(1)?;
            sort_payload(footprint, &array.index_sort, depth + 1)?;
            sort_payload(footprint, &array.element_sort, depth + 1)?;
        }
        Sort::Seq(element) => {
            footprint.allocation::<Sort>(1)?;
            sort_payload(footprint, element, depth + 1)?;
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            footprint.string(name)?;
        }
        Sort::Datatype(datatype) => {
            footprint.string(&datatype.name)?;
            footprint.allocation::<ay_core::DatatypeConstructor>(datatype.constructors.len())?;
            for constructor in &datatype.constructors {
                footprint.string(&constructor.name)?;
                footprint.allocation::<ay_core::DatatypeField>(constructor.fields.len())?;
                for field in &constructor.fields {
                    footprint.string(&field.name)?;
                    sort_payload(footprint, &field.sort, depth + 1)?;
                }
            }
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(_, _)
        | Sort::Char => {}
        _ => return Err(CheckpointCloneError::UnsupportedPayload),
    }
    Ok(())
}
