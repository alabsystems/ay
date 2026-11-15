// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored BOOLEAN-SKELETON refutation (#authored-skeleton-refutation).
//!
//! # The gap this closes
//!
//! `quantified_semantic_unsat_or_unknown` demands an authored-scope translated
//! refutation before a quantified query may publish `unsat`, and the
//! `authored_ground_core_refutes` leg — the one that says "this refutation used
//! no quantifier, so there is nothing to translate" — asks
//! `snapshot_ground_core` for the QUANTIFIER-FREE authored roots. On the
//! UltimateAutomizer `recHanoi03` shape
//!
//! ```smt2
//! (assert (and (<= |c_hanoi_#in~n| c_hanoi_~n) E))   ; E = (exists (x) phi)
//! (assert (not E))                                   ; the SAME term E
//! ```
//!
//! that set is EMPTY (`CERT/ground-core: authored=2 ground=0`), so the leg
//! declines, the negated-exists instantiation leg proposes ground witnesses the
//! probe cannot refute, and a query whose refutation is one resolution step
//! wide degrades to `unknown`.
//!
//! The refutation needs no quantifier reasoning and no theory reasoning at all.
//! `E` is derivable from the first root by `and_pos`; `(not E)` is the second
//! root; resolving them on the pivot `E` closes. What blocked it is that the
//! ground-core leg's notion of "no quantifier was used" is *syntactic* — a root
//! that MENTIONS a quantifier is dropped — where the right notion is
//! *positional*: a quantified subterm used only as an opaque Boolean atom is
//! not quantifier reasoning.
//!
//! # What this lane does
//!
//! Treat every maximal subterm as an opaque propositional atom and ask whether
//! the authored roots are already refuted by UNIT PROPAGATION over the
//! decomposition rules AY's strict checker validates. Three closing shapes, in
//! order:
//!
//! * **complementary units** — the authored `and`-conjunct closure contains
//!   both `T` and `(not T)`;
//! * **a falsified negated conjunction** — a closure member `(not (and C1..Ck))`
//!   every one of whose conjuncts is itself a closure member;
//! * **a falsified disjunction** — a closure member `(or D1..Dk)` every one of
//!   whose disjuncts has its complement in the closure.
//!
//! Each emits only `and_pos`, `not_and`, `or` and `resolution` steps over
//! authored terms, so the document is hole-free and every rule has both an AY
//! strict validator and a carcara 1.1.0 counterpart.
//!
//! # Soundness
//!
//! Nothing here is an abstraction or an over-approximation: every step is a
//! propositional consequence of the authored roots themselves, and the emitted
//! `assume`s are exactly authored roots (`consequence_unit` either assumes a
//! root or projects a conjunct out of one with `and_pos`). The producer's
//! findings are hints — the built candidate goes through
//! `install_consequence_replay_candidate`, which re-runs
//! `validate_reachable_assumes_in_problem_scope` over the exact authored scope,
//! the empty-clause check, and the full strict checker before installing it,
//! and the publication funnel mints and re-checks the same proof again. A
//! mis-built candidate can therefore only cost the firewall's `unknown` it was
//! already going to publish.
//!
//! # UNSAT-only
//!
//! Consulted at the quantified artifact firewall's downgrade and during
//! ordinary UNSAT proof assembly's authored-artifact prepass. The assembly
//! candidate remains local until the ordinary restoration and finalizer run.
//! Both require a checked authored refutation before `unknown -> unsat`. Kill switch
//! `--no-authored-skeleton-refutation` (and the parent `--no-consequence-replay`)
//! restores the baseline `unknown` byte-for-byte.

use super::*;

/// Authored-scope size beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Closure members scanned for a literal.
const MAX_CLOSURE_MEMBERS: usize = 4_096;
/// Conjuncts/disjuncts a single closing clause may carry.
const MAX_CLAUSE_WIDTH: usize = 64;
/// Clause-shaped members examined before the lane gives up.
const MAX_CLAUSE_CANDIDATES: usize = 256;
/// Attempts this lane may consume per public check-sat.
const MAX_LANE_ATTEMPTS: u8 = 1;

/// The closing shape the scan found, as a plan the builder replays.
enum SkeletonClosure {
    /// `T` and `(not T)` are both derivable units. Carries the two closure
    /// members, positive first.
    ComplementaryUnits { positive: TermId, negative: TermId },
    /// `(not (and C1..Ck))` is derivable and every `Ci` is too.
    FalsifiedNegatedAnd {
        member: TermId,
        conjuncts: Vec<TermId>,
    },
    /// `(or D1..Dk)` is derivable and every `Dj`'s complement is too.
    /// `complements[j]` is the closure member that refutes `disjuncts[j]`.
    FalsifiedOr {
        member: TermId,
        disjuncts: Vec<TermId>,
        complements: Vec<TermId>,
    },
}

impl Executor {
    /// Split `term` into `(atom, polarity)` for the propositional skeleton.
    fn skeleton_literal(&self, term: TermId) -> (TermId, bool) {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => (*inner, false),
            _ => (term, true),
        }
    }

    /// The `and` arguments of `term`, if it is an `and` application.
    fn skeleton_and_args(&self, term: TermId) -> Option<Vec<TermId>> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return None;
        };
        (name == "and").then(|| args.clone())
    }

    /// The `or` arguments of `term`, if it is an `or` application.
    fn skeleton_or_args(&self, term: TermId) -> Option<Vec<TermId>> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return None;
        };
        (name == "or").then(|| args.clone())
    }

    /// Artifact-firewall translation: refute the authored roots propositionally,
    /// treating every quantifier as an opaque Boolean atom, and install the
    /// resulting strict certificate as `last_proof`.
    ///
    /// Returns `true` only when a complete, scope-authorized, strict-checkable
    /// certificate was installed. On `false`, proof and premise authority are
    /// restored; diagnostics, memo entries and attempt accounting may advance.
    /// The caller keeps its fail-closed path.
    pub(in crate::executor) fn try_translate_authored_skeleton_refutation_unsat(&mut self) -> bool {
        self.with_authored_skeleton_refutation(|executor, candidate, _authored| {
            executor.install_consequence_replay_candidate(Some(candidate))
        })
    }

    /// Assembly variant: replace only the local candidate, before the normal
    /// authored-source restoration and finalizer. In particular, do not use
    /// the global installer here: its suppression reset belongs to the
    /// quantified translation path, not to a partially assembled document.
    pub(in crate::executor::proof) fn replace_with_authored_skeleton_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if !self.authored_skeleton_refutation_available()
            || self.skips_trust_elimination_repairs()
            || self.pending_nested_array_bool_bv_unsat.is_some()
            || self.pending_bounded_bv_lia_unsat.is_some()
            || self.proof_assembly_stop_requested()
            || self.authored_cascade_publishable(proof)
        {
            return;
        }
        let _committed = self.with_authored_skeleton_refutation(|executor, candidate, authored| {
            executor.commit_if_strictly_checked(proof, candidate, authored)
        });
    }

    fn authored_skeleton_refutation_available(&self) -> bool {
        crate::quant_unit_authority::authored_skeleton_refutation_enabled()
            && self.authored_skeleton_refutation_attempts.get() < MAX_LANE_ATTEMPTS
    }

    /// Share recognition, the single attempt allowance and exact-premise grant
    /// rollback. The caller supplies only its existing strict commit boundary:
    /// global installation for quantified translation, local replacement for
    /// assembly. Neither a declined candidate nor a declined commit keeps any
    /// new premise authority.
    fn with_authored_skeleton_refutation(
        &mut self,
        commit: impl FnOnce(&mut Self, Proof, &[TermId]) -> bool,
    ) -> bool {
        if !self.authored_skeleton_refutation_available() {
            return false;
        }
        let attempts = self.authored_skeleton_refutation_attempts.get();
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        self.authored_skeleton_refutation_attempts.set(attempts + 1);
        let Some(closure_plan) = self.plan_authored_skeleton_closure(&authored) else {
            replay_note(|| {
                "skeleton: decline: no propositional closure over authored roots".into()
            });
            return false;
        };
        let Some(candidate) = self.build_authored_skeleton_candidate(&authored, &closure_plan)
        else {
            replay_note(|| "skeleton: decline: candidate did not build".into());
            return false;
        };
        // (#authored-scope-premise-grant) Admit the exact authored roots this
        // candidate assumes as proof premises before the strict gate reads them.
        //
        // WHY IT IS NEEDED. `complete_problem_assertions_for_strict_proof`
        // assembles the obligation from the CURRENT assertion vector, and under
        // competition shedding that vector is AY's preprocessed residue, not the
        // authored problem. MEASURED on LIA `recHanoi03 …_557` in `--z3-mode`:
        // the authored roots are `[t25, t41]` while the strict obligation is
        // `[t476, t477]` — a quantifier-ELIMINATED pair
        // `(and (and (<= in~n 4) (<= (+ (- res) 15) 0)) (<= in~n ~n))` and its
        // negation, which is a formula nobody asserted. Without this grant the
        // strict checker refuses the certificate with "assumes term t25 outside
        // the supplied problem obligation" even though t25 IS an authored
        // assertion.
        //
        // WHY IT IS NOT A RELAXATION. Every recorded term is checked here to be
        // an EXACT member of `exact_concrete_authored_scope()` — the same
        // accessor `validate_reachable_assumes_in_problem_scope` is given at the
        // installation boundary — so the grant can only add the user's own
        // assertions, never a solver-derived one. This is the sanctioned ledger
        // (`record_rebuilt_authored_proof_premise`) five other authored-rebuild
        // lanes already use for the identical fact. The grant is reverted below
        // whenever the installation declines, so a rejected candidate leaves no
        // premise authority behind.
        let authored_set: ay_core::kani_compat::DetHashSet<TermId> =
            authored.iter().copied().collect();
        let mut assumed: Vec<TermId> = Vec::new();
        for step in &candidate.steps {
            if let ProofStep::Assume(term) = step {
                if !authored_set.contains(term) {
                    replay_note(|| {
                        "skeleton: decline: candidate assumes a non-authored term".into()
                    });
                    return false;
                }
                if !assumed.contains(term) {
                    assumed.push(*term);
                }
            }
        }
        let saved_rebuild_originals = self.last_proof_rebuild_originals.clone();
        for premise in assumed {
            self.record_rebuilt_authored_proof_premise(premise);
        }
        let committed = commit(self, candidate, &authored);
        if !committed {
            self.last_proof_rebuild_originals = saved_rebuild_originals;
        }
        replay_note(|| format!("skeleton: candidate committed={committed}"));
        committed
    }

    /// Scan the authored `and`-conjunct closure for a closing shape.
    ///
    /// Pure recognition: every returned plan is re-derived step by step by the
    /// builder and then re-checked by the strict checker.
    fn plan_authored_skeleton_closure(&self, authored: &[TermId]) -> Option<SkeletonClosure> {
        let closure = self.authored_and_conjunct_closure(authored);
        if closure.ordered.len() > MAX_CLOSURE_MEMBERS {
            return None;
        }
        // Pass 1: complementary units.
        let mut units: ay_core::kani_compat::DetHashMap<TermId, (bool, TermId)> =
            ay_core::kani_compat::DetHashMap::default();
        for &member in &closure.ordered {
            if self.ctx.terms.sort(member) != &Sort::Bool {
                continue;
            }
            let (atom, polarity) = self.skeleton_literal(member);
            match units.get(&atom) {
                Some(&(existing_polarity, existing_member)) => {
                    if existing_polarity != polarity {
                        let (positive, negative) = if polarity {
                            (member, existing_member)
                        } else {
                            (existing_member, member)
                        };
                        return Some(SkeletonClosure::ComplementaryUnits { positive, negative });
                    }
                }
                None => {
                    units.insert(atom, (polarity, member));
                }
            }
        }
        // Pass 2: a negated conjunction whose every conjunct is derivable, and
        // a disjunction whose every disjunct is refuted.
        let mut examined = 0usize;
        for &member in &closure.ordered {
            if examined >= MAX_CLAUSE_CANDIDATES {
                break;
            }
            if let TermData::Not(inner) = self.ctx.terms.get(member) {
                let inner = *inner;
                if let Some(conjuncts) = self.skeleton_and_args(inner) {
                    examined += 1;
                    if !conjuncts.is_empty()
                        && conjuncts.len() <= MAX_CLAUSE_WIDTH
                        && conjuncts
                            .iter()
                            .all(|conjunct| closure.contains(conjunct) && *conjunct != member)
                    {
                        return Some(SkeletonClosure::FalsifiedNegatedAnd { member, conjuncts });
                    }
                    continue;
                }
            }
            let Some(disjuncts) = self.skeleton_or_args(member) else {
                continue;
            };
            examined += 1;
            if disjuncts.is_empty() || disjuncts.len() > MAX_CLAUSE_WIDTH {
                continue;
            }
            let mut complements = Vec::with_capacity(disjuncts.len());
            for &disjunct in &disjuncts {
                let (atom, polarity) = self.skeleton_literal(disjunct);
                // The refuting closure member is the one asserting the OPPOSITE
                // literal: `atom` itself when the disjunct is negative, and the
                // existing raw negation when it is positive. Recognition must
                // not intern a missing complement: even a declined plan would
                // otherwise change the term inventory and subsequent IDs.
                let complement = if polarity {
                    match units.get(&atom) {
                        Some(&(false, negative_member)) => negative_member,
                        _ => {
                            complements.clear();
                            break;
                        }
                    }
                } else {
                    atom
                };
                if !closure.contains(&complement) || complement == member {
                    complements.clear();
                    break;
                }
                complements.push(complement);
            }
            if complements.len() == disjuncts.len() {
                return Some(SkeletonClosure::FalsifiedOr {
                    member,
                    disjuncts,
                    complements,
                });
            }
        }
        None
    }

    /// Replay a recognized closure as a strict Alethe derivation.
    fn build_authored_skeleton_candidate(
        &mut self,
        authored: &[TermId],
        closure: &SkeletonClosure,
    ) -> Option<Proof> {
        let authored_set: ay_core::kani_compat::DetHashSet<TermId> =
            authored.iter().copied().collect();
        let empty_plan: ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan> =
            ay_core::kani_compat::DetHashMap::default();
        let mut unit_ids: ay_core::kani_compat::DetHashMap<TermId, ProofId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut candidate = Proof::new();
        match closure {
            SkeletonClosure::ComplementaryUnits { positive, negative } => {
                let positive_unit = self.consequence_unit(
                    &mut candidate,
                    *positive,
                    &authored_set,
                    authored,
                    &empty_plan,
                    &mut unit_ids,
                )?;
                let negative_unit = self.consequence_unit(
                    &mut candidate,
                    *negative,
                    &authored_set,
                    authored,
                    &empty_plan,
                    &mut unit_ids,
                )?;
                candidate.add_resolution(Vec::new(), *positive, negative_unit, positive_unit);
            }
            SkeletonClosure::FalsifiedNegatedAnd { member, conjuncts } => {
                let member_unit = self.consequence_unit(
                    &mut candidate,
                    *member,
                    &authored_set,
                    authored,
                    &empty_plan,
                    &mut unit_ids,
                )?;
                let mut running: Vec<TermId> = conjuncts
                    .iter()
                    .map(|&conjunct| self.ctx.terms.mk_not_raw(conjunct))
                    .collect();
                let mut clause_step = candidate.add_rule_step(
                    AletheRule::NotAnd,
                    running.clone(),
                    vec![member_unit],
                    Vec::new(),
                );
                for &conjunct in conjuncts {
                    let conjunct_unit = self.consequence_unit(
                        &mut candidate,
                        conjunct,
                        &authored_set,
                        authored,
                        &empty_plan,
                        &mut unit_ids,
                    )?;
                    let negated = self.ctx.terms.mk_not_raw(conjunct);
                    let position = running.iter().position(|&lit| lit == negated)?;
                    let _ = running.remove(position);
                    clause_step = candidate.add_resolution(
                        running.clone(),
                        conjunct,
                        clause_step,
                        conjunct_unit,
                    );
                }
            }
            SkeletonClosure::FalsifiedOr {
                member,
                disjuncts,
                complements,
            } => {
                let member_unit = self.consequence_unit(
                    &mut candidate,
                    *member,
                    &authored_set,
                    authored,
                    &empty_plan,
                    &mut unit_ids,
                )?;
                let mut running = disjuncts.clone();
                let mut clause_step = candidate.add_rule_step(
                    AletheRule::Or,
                    running.clone(),
                    vec![member_unit],
                    Vec::new(),
                );
                for (&disjunct, &complement) in disjuncts.iter().zip(complements) {
                    let complement_unit = self.consequence_unit(
                        &mut candidate,
                        complement,
                        &authored_set,
                        authored,
                        &empty_plan,
                        &mut unit_ids,
                    )?;
                    let position = running.iter().position(|&lit| lit == disjunct)?;
                    let _ = running.remove(position);
                    // The pivot is the ATOM shared by the two clauses: the
                    // disjunct when it is positive, its stripped form when the
                    // complement is the atom itself.
                    let (pivot, disjunct_is_positive) = self.skeleton_literal(disjunct);
                    clause_step = if disjunct_is_positive {
                        candidate.add_resolution(
                            running.clone(),
                            pivot,
                            complement_unit,
                            clause_step,
                        )
                    } else {
                        candidate.add_resolution(
                            running.clone(),
                            pivot,
                            clause_step,
                            complement_unit,
                        )
                    };
                }
            }
        }
        Some(candidate)
    }
}

#[cfg(test)]
mod tests;
