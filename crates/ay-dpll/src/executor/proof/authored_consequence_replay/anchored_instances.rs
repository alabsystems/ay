// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Anchored-first consequence replay (#consequence-replay-anchored-instances).
//!
//! THE COST THIS REMOVES. The same-context probe re-decides EVERY recorded
//! instance of every derivable universal (up to `MAX_INSTANCES`), and the
//! recording lanes do not only record the instances a refutation needs:
//! enumerative instantiation also records one instance per ground term of the
//! binder's sort. On the array-frame self-check fixture
//! (`frame_quantifier_instance_resolve`) that is 14 instances of
//! `forall k. snew[k] = ite(k = 1, val, s[k])`, at
//! `k := 0, 1, 2, val, s[0], 10, s[1], 20, s[2], 30, snew[0], snew[1],
//! snew[2], -1`. Only `k := 0, 1, 2` touch anything else in the consequence
//! set; every other instance contributes nothing but two FRESH array reads
//! `snew[t]`, `s[t]` over an index no other consequence mentions. They grow the
//! probe's per-array index set from 4 to 15, and the array/arithmetic
//! combination pays for every index pair: measured on a dev build
//! (opt-level 1) the window-scoped probe spent 1.34 s to a fused Generic
//! conflict the strict checker must refuse, and the unscoped retry
//! (#frame-probe-unscoped-retry) then needed a further 4.46 s — 5.9 s against
//! the 5 s query envelope, so the correct `unsat` published as `unknown`. The
//! same probe over the anchored subset returns a strict-complete proof,
//! window-scoped, in 31 ms.
//!
//! THE FIX IS AN ORDERING, NOT A NEW AUTHORITY. The anchored subset is tried
//! first, and the whole consequence set is re-decided under the same authority
//! as before (on a term store the anchored probe may have extended) whenever
//! the subset does not yield a stitched strict proof. A forall
//! instance is ANCHORED when a term it creates by substitution — a compound
//! subterm that mentions one of its binder values, other than a subterm of the
//! binder values themselves — already occurs in the non-instance consequences
//! (quantifier-free authored conjuncts and Skolem instances) or in an
//! instance anchored earlier; this is E-matching's relevance criterion, with
//! every binder-mentioning read of the instance acting as a trigger.
//!
//! SOUNDNESS. The anchored set is a SUBSET of the consequence set, each member
//! a sound consequence of the authored problem, so its refutation is a
//! refutation of the authored problem. Its proof passes the same probe strict
//! checker, the same stitcher, and the same outer strict re-check as a
//! whole-set proof; nothing is published on the subset's word. The subset can
//! only fail to refute, and then the whole set is probed as before.
//!
//! BUDGET. The anchored attempt makes exactly ONE window-scoped probe claim,
//! never the unscoped retry, at a quarter of the plan's per-probe cap (at most
//! 1250 ms and 60 round trips of the 5000 ms / 240 round-trip envelope), so a
//! subset that fails to refute costs the whole-set probe after it at most that
//! one grant: on a fresh envelope the whole-set probe keeps at least 3750 ms
//! and 180 round trips.

use super::*;

/// Shared allowance for node, edge, binder, fixed-point, and output scans.
const MAX_ANCHOR_WORK: usize = 65_536;

/// Share of the plan's per-probe cap the anchored attempt's single claim may
/// take, as a divisor, in both currencies: 1250 ms and 60 round trips of a
/// positive-Skolem plan's 5 s and 240, 500 ms and 16 of a standard plan's 2 s
/// and 64. Every anchored refutation measured in the test suites
/// needed at most 149 ms on a dev build; a subset that does not refute that
/// quickly is not the cheap first try this lane is for, and must leave the
/// whole-set probe most of the envelope.
const ANCHORED_PROBE_CAP_DIVISOR: u64 = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AnchorFailure {
    WorkLimit,
    Stopped(crate::UnknownReason),
}

/// Terminal control refusal, distinct from a local relevance-work decline.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct AnchorStopped;

struct AnchorWork<'a, F> {
    remaining: usize,
    stop: &'a mut F,
}

impl<F: FnMut() -> Option<crate::UnknownReason>> AnchorWork<'_, F> {
    fn poll(&mut self) -> Result<(), AnchorFailure> {
        match (self.stop)() {
            Some(reason) => Err(AnchorFailure::Stopped(reason)),
            None => Ok(()),
        }
    }

    fn charge(&mut self, amount: usize) -> Result<(), AnchorFailure> {
        self.poll()?;
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(AnchorFailure::WorkLimit)?;
        Ok(())
    }
}

/// Borrowed children in exactly TermStore::children order, without its Vec clone.
struct AnchorChildren<'a> {
    args: &'a [TermId],
    bindings: &'a [(String, TermId)],
    tail: [Option<TermId>; 3],
}

impl<'a> AnchorChildren<'a> {
    fn new(terms: &'a TermStore, term: TermId) -> Result<Self, AnchorFailure> {
        let mut children = Self {
            args: &[],
            bindings: &[],
            tail: [None; 3],
        };
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => children.args = args,
            TermData::Let(bindings, body) => {
                children.bindings = bindings;
                children.tail[0] = Some(*body);
            }
            TermData::Not(term) | TermData::Forall(_, term, _) | TermData::Exists(_, term, _) => {
                children.tail[0] = Some(*term);
            }
            TermData::Ite(c, t, e) => children.tail = [Some(*c), Some(*t), Some(*e)],
            _ => return Err(AnchorFailure::WorkLimit),
        }
        Ok(children)
    }

    fn precharge<F: FnMut() -> Option<crate::UnknownReason>>(
        &self,
        work: &mut AnchorWork<'_, F>,
    ) -> Result<usize, AnchorFailure> {
        let count = self
            .args
            .len()
            .checked_add(self.bindings.len())
            .and_then(|count| count.checked_add(self.tail.iter().flatten().count()))
            .ok_or(AnchorFailure::WorkLimit)?;
        work.charge(count)?;
        Ok(count)
    }

    fn iter(&self) -> impl Iterator<Item = TermId> + '_ {
        self.args
            .iter()
            .copied()
            .chain(self.bindings.iter().map(|(_, term)| *term))
            .chain(self.tail.iter().flatten().copied())
    }
}

fn collect_subterms<F: FnMut() -> Option<crate::UnknownReason>>(
    terms: &TermStore,
    root: TermId,
    out: &mut ay_core::kani_compat::DetHashSet<TermId>,
    work: &mut AnchorWork<'_, F>,
) -> Result<(), AnchorFailure> {
    work.charge(1)?;
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        work.charge(1)?;
        if !out.insert(term) {
            continue;
        }
        let children = AnchorChildren::new(terms, term)?;
        children.precharge(work)?;
        for child in children.iter() {
            work.poll()?;
            stack.push(child);
        }
    }
    Ok(())
}

fn instantiated_terms<F: FnMut() -> Option<crate::UnknownReason>>(
    terms: &TermStore,
    instance: TermId,
    binding: &[TermId],
    work: &mut AnchorWork<'_, F>,
) -> Result<Vec<TermId>, AnchorFailure> {
    work.charge(binding.len())?;
    let mut binder_parts = ay_core::kani_compat::DetHashSet::default();
    for &value in binding {
        collect_subterms(terms, value, &mut binder_parts, work)?;
    }
    let mut mentions: ay_core::kani_compat::DetHashMap<TermId, bool> =
        ay_core::kani_compat::DetHashMap::default();
    let mut created = Vec::new();
    work.charge(1)?;
    let mut stack = vec![(instance, false)];
    while let Some((term, children_done)) = stack.pop() {
        work.charge(1)?;
        if mentions.contains_key(&term) {
            continue;
        }
        let children = AnchorChildren::new(terms, term)?;
        // Price every edge, including repeated edges, before any stack growth.
        let child_count = children.precharge(work)?;
        if !children_done {
            work.charge(1)?;
            stack.push((term, true));
            for child in children.iter() {
                work.poll()?;
                if !mentions.contains_key(&child) {
                    stack.push((child, false));
                }
            }
            continue;
        }
        work.charge(binding.len())?;
        let mut mentions_binder = false;
        for value in binding {
            work.poll()?;
            if *value == term {
                mentions_binder = true;
                break;
            }
        }
        if !mentions_binder {
            for child in children.iter() {
                work.poll()?;
                if mentions.get(&child).copied().unwrap_or(false) {
                    mentions_binder = true;
                    break;
                }
            }
        }
        work.charge(1)?;
        mentions.insert(term, mentions_binder);
        if mentions_binder && child_count != 0 && !binder_parts.contains(&term) {
            work.charge(1)?;
            created.push(term);
        }
    }
    Ok(created)
}

/// Partition one relevance round without refunding skipped or duplicate scans.
fn anchor_round<F: FnMut() -> Option<crate::UnknownReason>>(
    unanchored: Vec<(TermId, Vec<TermId>)>,
    known: &ay_core::kani_compat::DetHashSet<TermId>,
    work: &mut AnchorWork<'_, F>,
) -> Result<(Vec<(TermId, Vec<TermId>)>, Vec<(TermId, Vec<TermId>)>), AnchorFailure> {
    work.charge(unanchored.len())?;
    let mut anchored = Vec::new();
    let mut pending = Vec::new();
    for item in unanchored {
        work.charge(item.1.len())?;
        let mut linked = false;
        for term in &item.1 {
            work.poll()?;
            if known.contains(term) {
                linked = true;
                break;
            }
        }
        if linked {
            anchored.push(item);
        } else {
            pending.push(item);
        }
    }
    Ok((anchored, pending))
}

fn anchored_consequence_subset<F: FnMut() -> Option<crate::UnknownReason>>(
    terms: &TermStore,
    consequences: &[TermId],
    plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
    authored_conjuncts: &AndConjunctClosure,
    work: &mut AnchorWork<'_, F>,
) -> Result<Option<Vec<TermId>>, AnchorFailure> {
    work.charge(consequences.len())?;
    let mut known = ay_core::kani_compat::DetHashSet::default();
    let mut kept = ay_core::kani_compat::DetHashSet::default();
    let mut anchored_instances = 0usize;
    let mut unanchored: Vec<(TermId, Vec<TermId>)> = Vec::new();
    for &consequence in consequences {
        work.poll()?;
        let binding = match plans.get(&consequence) {
            Some(ConsequencePlan::ForallInstance { binding, .. })
                if !authored_conjuncts.contains(&consequence) =>
            {
                binding
            }
            _ => {
                kept.insert(consequence);
                collect_subterms(terms, consequence, &mut known, work)?;
                continue;
            }
        };
        let created = instantiated_terms(terms, consequence, binding, work)?;
        if created.is_empty() {
            kept.insert(consequence);
            anchored_instances += 1;
            collect_subterms(terms, consequence, &mut known, work)?;
        } else {
            unanchored.push((consequence, created));
        }
    }
    loop {
        let (anchored, pending) = anchor_round(unanchored, &known, work)?;
        unanchored = pending;
        if anchored.is_empty() {
            break;
        }
        work.charge(anchored.len())?;
        for (instance, _) in anchored {
            kept.insert(instance);
            anchored_instances += 1;
            collect_subterms(terms, instance, &mut known, work)?;
        }
    }
    if anchored_instances == 0 || unanchored.is_empty() {
        return Ok(None);
    }
    work.charge(consequences.len())?;
    let mut subset = Vec::new();
    for &consequence in consequences {
        work.poll()?;
        if kept.contains(&consequence) {
            subset.push(consequence);
        }
    }
    Ok(Some(subset))
}

impl Executor {
    fn anchored_replay_open(&mut self) -> bool {
        use crate::UnknownOrigin;
        !matches!(
            self.last_unknown_reason.map(crate::UnknownReason::origin),
            Some(
                UnknownOrigin::InterruptFlag
                    | UnknownOrigin::SolveDeadline
                    | UnknownOrigin::MemoryBudget
                    | UnknownOrigin::DeterministicResourceBudget
            )
        ) && !self.should_abort_theory_loop()
    }

    fn finish_anchor_selection(
        &mut self,
        selection: Result<Option<Vec<TermId>>, AnchorFailure>,
    ) -> Result<Option<Vec<TermId>>, AnchorStopped> {
        if let Err(AnchorFailure::Stopped(reason)) = selection {
            // Retain the observed reason even if the live control recovered.
            self.record_unknown_from_origin(reason.origin());
            self.last_result = Some(SolveResult::Unknown);
            return Err(AnchorStopped);
        }
        if !self.anchored_replay_open() {
            return Err(AnchorStopped);
        }
        match selection {
            Ok(subset) => Ok(subset),
            Err(AnchorFailure::WorkLimit) => Ok(None),
            Err(AnchorFailure::Stopped(_)) => Err(AnchorStopped),
        }
    }

    /// A local scan cap declines ordinarily; an observed stop forbids fallback.
    pub(super) fn try_anchored_consequence_replay(
        &mut self,
        consequences: &[TermId],
        plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        authored_conjuncts: &AndConjunctClosure,
        authored: &[TermId],
        per_probe_cap: consequence_replay_budget::ProbeCap,
    ) -> Result<Option<Proof>, AnchorStopped> {
        if !self.anchored_replay_open() {
            return Err(AnchorStopped);
        }
        let selection = {
            let mut stop = || self.external_stop_reason();
            let mut work = AnchorWork {
                remaining: MAX_ANCHOR_WORK,
                stop: &mut stop,
            };
            anchored_consequence_subset(
                &self.ctx.terms,
                consequences,
                plans,
                authored_conjuncts,
                &mut work,
            )
        };
        let Some(anchored) = self.finish_anchor_selection(selection)? else {
            return Ok(None);
        };
        replay_note(|| {
            format!(
            "anchored-first probe: {} of {} consequences ({} unanchored instances deferred to the whole-set probe)",
            anchored.len(), consequences.len(), consequences.len() - anchored.len())
        });
        let probe_proof = self.metered_scoped_consequence_replay_probe(
            &anchored,
            per_probe_cap.share(ANCHORED_PROBE_CAP_DIVISOR),
        );
        if !self.anchored_replay_open() {
            return Err(AnchorStopped);
        }
        let Some(probe_proof) = probe_proof else {
            return Ok(None);
        };
        let stitched = self.stitch_consequence_replay(&probe_proof, authored, plans);
        if !self.anchored_replay_open() {
            return Err(AnchorStopped);
        }
        if stitched.is_none() {
            replay_note(|| {
                format!(
                    "anchored-first stitch failed over {} probe steps",
                    probe_proof.steps.len()
                )
            });
        }
        Ok(stitched)
    }
}

#[cfg(test)]
#[path = "anchored_instances_tests.rs"]
mod tests;
