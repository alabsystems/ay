// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-Based Quantifier Instantiation (MBQI).
//!
//! Implements the quick-check phase of Z3's MBQI algorithm (Ge & de Moura, CAV 2009).
//! After E-matching and CEGQI, if the ground solver returns SAT but unhandled
//! universal quantifiers remain, MBQI evaluates each quantifier body under the
//! candidate model with ground term substitutions. If the body evaluates to false
//! for some ground term combination, that instantiation is a counterexample —
//! the ground lemma is added and the solver re-checks.
//!
//! When no existing ground terms are available for a variable's sort, MBQI
//! synthesizes default candidates from the model (model value injection).
//! For interpreted sorts (Int, Real, BV, etc.) this uses theory defaults (0, 0.0,
//! etc.) plus model-assigned values. For uninterpreted sorts, the EUF model's
//! sort universe provides concrete element constants.
//!
//! Reference: Z3 `sat/smt/q_mbi.cpp` (quick_check, check_forall,
//! replace_model_value, add_universe_restriction).
//!
//! Unlike CEGQI, MBQI does NOT inject CE lemma variables into the assertion set.
//! It produces ground instantiations only, avoiding CE-lemma interaction bugs
//! (#6045, #5975).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermEntryStamp;
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

use super::model::{CertifiedConstInterpEntry, CertifiedConstInterpReadError, EvalValue, Model};
use super::quantifier_loop::result_mapping::CheckedGroundDecision;
use super::Executor;
use crate::ematching::{contains_quantifier, subst_vars};
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

/// Maximum MBQI refinement rounds before giving up.
const MAX_MBQI_ROUNDS: usize = 5;

/// Maximum candidate substitutions per quantifier per round.
/// Prevents combinatorial explosion for multi-variable quantifiers with many
/// ground terms per sort.
const MAX_QUICK_CHECK_CANDIDATES: usize = 1000;

/// Maximum number of synthesized default candidates per sort.
/// Keeps model value injection bounded for sorts with many model values.
const MAX_SYNTHESIZED_CANDIDATES: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UfCompletionEval {
    True,
    False,
    Unknown,
}

/// Result of the restored-quantifier MBQI soundness gate.
///
/// The quick checker samples interpreted infinite domains; exhausting those
/// samples is not a proof that a universal holds.  Keep that outcome distinct
/// from both a genuinely empty obligation set and an exhaustively enumerated
/// finite domain so callers cannot turn "no sampled counterexample" into SAT.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum SkippedQuantifierMbqiGate {
    /// The restored assertion window contains no top-level universal.
    NoQuantifiers,
    /// Every value of every binder domain was checked and evaluated true.
    ExhaustivelySatisfied,
    /// Sampling found no decisive refutation, but did not exhaust the domains.
    Inconclusive,
}

/// The two residue cases in the exact closed parity theorem admitted by
/// [`Executor::try_valid_closed_sentence_sat_certificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactClosedParityResidue {
    Binder,
    Successor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactClosedUnboundedLower {
    Universal,
    Literal,
}

/// Checked authority for one exact structural closed-sentence theorem window.
///
/// Construction is private to the structural checker. The type deliberately
/// does not implement `Clone`, and its ordered roots cannot be supplied or
/// retargeted by a caller. The query-authority module must consume it before it
/// can install the shared MBQI publication grant.
#[must_use = "exact closed-sentence SAT evidence must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactClosedSentenceSat {
    query_epoch: crate::executor::QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
}

/// Checked authority for one datatype quantified-SAT certificate.
///
/// Only certificate producers in this module can construct this token.  The
/// query-authority boundary consumes it and rechecks its immutable query,
/// source, and root identities before installing publication authority.
#[must_use = "checked datatype SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedDtSatAuthority {
    query_epoch: crate::executor::QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
    projection_bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
    model_epoch: super::model::QuantifiedGrantModelEpoch,
}

impl CheckedDtSatAuthority {
    fn for_current(
        executor: &mut Executor,
        roots: &[TermId],
        projection_bindings: Vec<ay_frontend::CheckedProjectionBinding>,
    ) -> Option<Self> {
        if projection_bindings
            .iter()
            .any(|binding| !executor.ctx.projection_binding_still_current(binding))
        {
            return None;
        }
        let mut model = executor.last_model.take()?;
        if !executor.complete_quantified_output_model_before_seal(&mut model, roots) {
            executor.last_model = Some(model);
            return None;
        }
        executor.last_model = Some(model);
        // Completion evaluates an uninstalled candidate in an isolated memo
        // scope and restores the predecessor cache on return. Publishing that
        // candidate changes the model identity, so no predecessor entry may
        // survive the commit even when this constructor runs inside an outer
        // validation session.
        super::model::eval_memo_clear();
        let model_epoch = executor.last_model.as_mut()?.seal_quantified_grant_model();
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            projection_bindings: projection_bindings.into_boxed_slice(),
            model_epoch,
        })
    }

    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &Executor,
    ) -> Option<(
        Box<[TermId]>,
        super::model::QuantifiedGrantModelEpoch,
        Box<[ay_frontend::CheckedProjectionBinding]>,
    )> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.root_entries.iter().all(Option::is_some)
            && self.root_entries.iter().copied().eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self
                .projection_bindings
                .iter()
                .all(|binding| executor.ctx.projection_binding_still_current(binding))
            && executor
                .last_model
                .as_ref()
                .is_some_and(|model| model.carries_quantified_grant_model(&self.model_epoch)))
        .then_some((self.roots, self.model_epoch, self.projection_bindings))
    }

    #[cfg(test)]
    pub(in crate::executor) fn for_test(executor: &mut Executor, roots: &[TermId]) -> Option<Self> {
        Self::for_current(executor, roots, Vec::new())
    }
}

/// Checked authority for one model-based quantified-SAT certificate.
///
/// This is deliberately distinct from datatype and exact-closed-sentence
/// evidence so a caller cannot relabel one proof class as another.  It is
/// linear and its constructor remains private to the MBQI certificate module.
#[must_use = "checked MBQI SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedMbqiSatAuthority {
    query_epoch: crate::executor::QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
    /// Positive declaration identity/kind/signature evidence for proof classes
    /// that reinterpret authored UF heads.  The finite-domain MBQI theorem does
    /// not reinterpret a declaration and therefore carries `None` here.
    projection_bindings: Option<ay_frontend::CheckedProjectionBindings>,
    model_epoch: super::model::QuantifiedGrantModelEpoch,
}

impl CheckedMbqiSatAuthority {
    fn for_current(executor: &mut Executor, roots: &[TermId]) -> Option<Self> {
        Self::for_current_with_projection_bindings(executor, roots, None)
    }

    fn for_current_with_projection_bindings(
        executor: &mut Executor,
        roots: &[TermId],
        projection_bindings: Option<ay_frontend::CheckedProjectionBindings>,
    ) -> Option<Self> {
        if projection_bindings.as_ref().is_some_and(|bindings| {
            !executor
                .ctx
                .projection_bindings_still_current(bindings, roots)
        }) {
            return None;
        }
        let mut model = executor.last_model.take()?;
        if !executor.complete_quantified_output_model_before_seal(&mut model, roots) {
            executor.last_model = Some(model);
            return None;
        }
        executor.last_model = Some(model);
        // See the datatype authority constructor above: installing the
        // completed candidate invalidates every memoized predecessor value.
        super::model::eval_memo_clear();
        let model_epoch = executor.last_model.as_mut()?.seal_quantified_grant_model();
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            projection_bindings,
            model_epoch,
        })
    }

    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &Executor,
    ) -> Option<(
        Box<[TermId]>,
        super::model::QuantifiedGrantModelEpoch,
        Option<ay_frontend::CheckedProjectionBindings>,
    )> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.root_entries.iter().all(Option::is_some)
            && self.root_entries.iter().copied().eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self.projection_bindings.as_ref().is_none_or(|bindings| {
                executor
                    .ctx
                    .projection_bindings_still_current(bindings, &self.roots)
            })
            && executor
                .last_model
                .as_ref()
                .is_some_and(|model| model.carries_quantified_grant_model(&self.model_epoch)))
        .then_some((self.roots, self.model_epoch, self.projection_bindings))
    }

    #[cfg(test)]
    pub(in crate::executor) fn for_test(executor: &mut Executor, roots: &[TermId]) -> Option<Self> {
        Self::for_current(executor, roots)
    }
}

impl CheckedExactClosedSentenceSat {
    fn for_current(executor: &Executor, roots: &[TermId]) -> Self {
        Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
        }
    }

    /// Consume this evidence and release its exact checked roots only while
    /// the public query and frontend source/scope identities remain current.
    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &Executor,
    ) -> Option<Box<[TermId]>> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.root_entries.iter().all(Option::is_some)
            && self.root_entries.iter().copied().eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))))
        .then_some(self.roots)
    }
}

/// Core operators whose interpreted identities are load-bearing for the exact
/// closed-sentence theorems. Any source declaration using one of these
/// spellings makes the structural certificate decline, even when elaboration
/// assigned that declaration a disjoint internal name.
const EXACT_CLOSED_SENTENCE_OPERATORS: [&str; 6] = ["or", "=", "mod", "+", "and", "<"];

/// Materialized role of a CONSTRAINED head symbol in the left-inverse SAT
/// certificate (#2774, `mbqi_sat_validated_left_inverse_axioms`). Every skipped
/// forall the certificate accepts pins exactly one interpretation for its head
/// symbol(s); the functionalized re-evaluator (`left_inverse_reeval`) then
/// evaluates every ground occurrence of that head UNDER THE MATERIALIZED
/// interpretation — never under the (lossy) extracted model tables.
#[derive(Debug, Clone, PartialEq, Eq)]
enum LiRole {
    /// `Box` of a `forall x:S. Unbox(Box x) = x` axiom. Materialized as the
    /// TOTAL INJECTIVE embedding `a ↦ BoxPoint(box_sym, a)` of the binder
    /// domain into the (uninterpreted, enlargeable) result sort's universe.
    Box,
    /// `Unbox` of a left-inverse axiom. Materialized as the inverse of its
    /// partner `Box` on the `BoxPoint` family, and as the designated
    /// per-sort fallback value everywhere else (see `left_inverse_fallback`).
    Unbox {
        /// The partner `Box` symbol whose `BoxPoint`s this head inverts.
        box_sym: Symbol,
        /// The axiom's binder sort `S` = this head's result sort (fixed by
        /// well-sortedness of `Unbox(Box x) = x`), used to pick the fallback.
        result_sort: Sort,
    },
    /// Head `f` of a unary identity definition `forall x:T. f(x) = x`.
    /// Materialized as the identity function on `T` (over ANY universe).
    Identity,
}

/// An element of an uninterpreted sort's universe in the EXPLICITLY
/// CONSTRUCTED model `M'` the left-inverse certificate exhibits. The three
/// variants are PAIRWISE-DISTINCT elements by construction (`M'`'s universe
/// for a sort is the disjoint union of the extracted-model elements adopted
/// for free constants and uninterpreted-function points, the per-Box-symbol
/// `BoxPoint` families, and one designated fallback padding element), so
/// derived structural equality IS element equality in `M'`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LiElem {
    /// `Box(a)` for `Box` a constrained left-inverse inner head and `a` a
    /// definite binder-domain value: one fresh universe element PER DOMAIN
    /// POINT, tagged by the `Box` symbol name. Injectivity of the materialized
    /// `Box` and disjointness across distinct `Box` symbols are structural.
    BoxPoint(Symbol, Box<LiValue>),
    /// An element name adopted from the extracted model for a FREE CONSTANT
    /// or an UNCONSTRAINED-UF ground point of the uninterpreted sort (tagged
    /// `(sort, element)`). The adoption is a free CHOICE of assignment for
    /// `M'` — every assertion is re-checked under it, so no extraction
    /// lossiness is trusted.
    Extracted(String, String),
    /// The single designated padding element of the sort (used as the
    /// off-image fallback value of `Unbox` heads with an uninterpreted result
    /// sort). Distinct from every `BoxPoint` and every `Extracted` element.
    Fallback(String),
}

/// A DEFINITE value in the constructed model `M'` of the left-inverse SAT
/// certificate. Anything the re-evaluator cannot pin to one of these declines
/// (fail closed). Derived structural equality is exact value equality in `M'`
/// (interpreted values are canonical; `LiElem` variants are pairwise-distinct
/// universe elements by construction). `Hash` keys the constructed
/// uninterpreted-function tables ([`LiUfKey`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LiValue {
    /// A Boolean.
    Bool(bool),
    /// A bitvector value (canonical, in `[0, 2^width)`).
    BitVec {
        /// The numeric value.
        value: num_bigint::BigInt,
        /// The bit width.
        width: u32,
    },
    /// An integer.
    Int(num_bigint::BigInt),
    /// An element of an uninterpreted sort's universe.
    Elem(LiElem),
}

/// One point of a constructed UNCONSTRAINED-UF interpretation in `M'`:
/// `(symbol name, argument values)`. The certificate builds these tables
/// itself (the UF-graph adoption fixpoint in
/// `Executor::mbqi_sat_validated_left_inverse_axioms`): one entry per
/// distinct application point, so the interpretation is FUNCTIONAL by
/// construction — never read off the extracted model's (lossy, possibly
/// congruence-incoherent) per-term values without that guarantee.
type LiUfKey = (Symbol, Vec<LiValue>);

impl Executor {
    /// Run MBQI refinement loop: check unhandled quantifiers against the current
    /// model, add counterexample instantiations, and re-solve.
    ///
    /// Called from `map_quantifier_result` when the ground solver returns SAT
    /// but unhandled universal quantifiers remain. Returns the final solve result
    /// after MBQI refinement, or `None` if MBQI found no counterexamples
    /// (indicating the SAT result may be genuine or MBQI is incomplete).
    ///
    /// # Arguments
    /// * `unhandled_quantifiers` - Universal quantifiers not covered by E-matching/CEGQI
    /// * `category` - Logic category for the re-solve dispatch
    pub(in crate::executor) fn try_mbqi_refinement(
        &mut self,
        unhandled_quantifiers: &[TermId],
        category: LogicCategory,
        authority_roots: &[TermId],
    ) -> Option<Result<SolveResult>> {
        if unhandled_quantifiers.is_empty() {
            return None;
        }

        // Any Sat produced below is a sample unless BV-MBQI proves otherwise.
        self.revoke_bv_full_domain_sat_authority();

        // Only process universal quantifiers, excluding any marked "E-matching
        // only" (`mark_no_mbqi`) — those must not be MBQI-discharged (they fail
        // closed to Unknown at the quantifier-loop caller instead).
        let forall_quants: Vec<TermId> = unhandled_quantifiers
            .iter()
            .copied()
            .filter(|&q| {
                matches!(self.ctx.terms.get(q), TermData::Forall(..))
                    && !self.ctx.terms.is_no_mbqi(q)
            })
            .collect();

        if forall_quants.is_empty() {
            return None;
        }

        // Partition into BV-only and other quantifiers. Try BV-specific MBQI
        // first for BV quantifiers (better boundary heuristics), then fall
        // back to generic MBQI for the rest.
        let (bv_quants, other_quants) =
            super::bv_mbqi::partition_bv_quantifiers(&self.ctx.terms, &forall_quants);

        if !bv_quants.is_empty() {
            if let Some(result) = self.try_bv_mbqi_refinement(&bv_quants, category, authority_roots)
            {
                match result {
                    Ok(SolveResult::Unsat(_)) => return Some(result),
                    Ok(SolveResult::Sat) if other_quants.is_empty() => return Some(result),
                    // BV-MBQI returned SAT but there are non-BV quantifiers remaining —
                    // fall through to generic MBQI for those. The BV proof does
                    // not cover them, so the certificate is withdrawn.
                    Ok(SolveResult::Sat) => {
                        self.revoke_bv_full_domain_sat_authority();
                    }
                    other => return Some(other),
                }
            }
        }

        // If all quantifiers were BV-only and BV-MBQI didn't find counterexamples,
        // skip the generic path.
        if other_quants.is_empty() && !bv_quants.is_empty() {
            return None;
        }

        // Use the remaining quantifiers (or all if none were BV-only) for generic MBQI.
        let quants_for_generic = if bv_quants.is_empty() {
            &forall_quants
        } else {
            &other_quants
        };

        let mut seen_instantiations: HashSet<TermId> = HashSet::default();

        // Does any quantifier here have UF-definition shape? Gates the (cheap
        // but not free) `occurring_ground` scan below.
        let any_definitional = quants_for_generic
            .iter()
            .any(|&q| match self.ctx.terms.get(q) {
                TermData::Forall(vars, body, _) => {
                    let (vars, body) = (vars.clone(), *body);
                    self.forall_uf_definition_head(&vars, body).is_some()
                }
                _ => false,
            });

        for _round in 0..MAX_MBQI_ROUNDS {
            // Collect ground terms by sort from current assertions.
            let ground_by_sort = crate::ematching::collect_ground_terms_by_sort(
                &self.ctx.terms,
                &self.ctx.assertions,
            );

            // Collect sorts that need synthesized candidates: sorts that appear
            // as bound variable sorts in our quantifiers but have no ground terms.
            let needed_sorts: HashSet<Sort> = quants_for_generic
                .iter()
                .filter_map(|&q| match self.ctx.terms.get(q) {
                    TermData::Forall(vars, _, _) => Some(vars.clone()),
                    _ => None,
                })
                .flatten()
                .map(|(_, sort)| sort)
                .filter(|sort| ground_by_sort.get(sort).is_none_or(Vec::is_empty))
                .collect();

            // Synthesize default candidates for sorts with no ground terms.
            let synthesized = if needed_sorts.is_empty() {
                HashMap::default()
            } else {
                self.synthesize_mbqi_candidates(&needed_sorts)
            };

            let mut new_instantiations: Vec<TermId> = Vec::new();
            let mut all_satisfied = true;

            // Ground terms that actually OCCUR in the current assertion set
            // (same collection as the candidate universe, flattened for O(1)
            // membership). Used by the phantom-counterexample guard below; it
            // tracks the current round because genuine instantiations added in
            // an earlier round make their head points occur.
            let occurring_ground: HashSet<TermId> = if any_definitional {
                ground_by_sort.values().flatten().copied().collect()
            } else {
                HashSet::default()
            };

            for &quant in quants_for_generic {
                let (vars, body) = match self.ctx.terms.get(quant) {
                    TermData::Forall(v, b, _) => (v.clone(), *b),
                    _ => continue,
                };

                if vars.is_empty() {
                    continue;
                }

                // The defined head `f(x⃗)` when this `forall` is a UF DEFINITION
                // (see `forall_uf_definition_head`); `None` otherwise.
                let definition_head = self.forall_uf_definition_head(&vars, body);

                // Collect candidate terms per variable. Fall back to synthesized
                // defaults when no existing ground terms are available (#5971).
                let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
                let mut any_empty = false;
                for (_name, sort) in vars.iter() {
                    let mut candidates = ground_by_sort.get(sort).cloned().unwrap_or_default();
                    if candidates.is_empty() {
                        candidates = synthesized.get(sort).cloned().unwrap_or_default();
                    }
                    if candidates.is_empty() {
                        any_empty = true;
                        break;
                    }
                    candidates_per_var.push(candidates);
                }
                if any_empty {
                    all_satisfied = false;
                    continue;
                }

                let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

                // Enumerate substitutions (cartesian product with budget).
                let mut indices: Vec<usize> = vec![0; vars.len()];
                let mut checked = 0usize;
                let mut quant_all_true = true;

                loop {
                    if checked >= MAX_QUICK_CHECK_CANDIDATES {
                        quant_all_true = false;
                        all_satisfied = false;
                        break;
                    }

                    // Build binding.
                    let binding: Vec<TermId> = indices
                        .iter()
                        .enumerate()
                        .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
                        .collect();

                    // Create ground instance via substitution (hash-consed, cheap).
                    let subst_map: HashMap<String, TermId> = var_names
                        .iter()
                        .zip(binding.iter())
                        .map(|(name, &t)| (name.clone(), t))
                        .collect();
                    let ground_body = subst_vars(&mut self.ctx.terms, body, &subst_map);

                    // Evaluate under the model.
                    // Re-borrow model each iteration to satisfy the borrow checker
                    // (subst_vars borrows &mut self.ctx.terms above).
                    let eval = if let Some(ref model) = self.last_model {
                        self.evaluate_term(model, ground_body)
                    } else {
                        EvalValue::Unknown
                    };

                    match eval {
                        EvalValue::Bool(true) => {
                            // Satisfies the quantifier — continue.
                        }
                        EvalValue::Bool(false) => {
                            // PHANTOM-COUNTEREXAMPLE GUARD (#mbqi-matching-loop).
                            //
                            // For a UF DEFINITION `forall x⃗. (= (f x⃗) body(x⃗))`, the
                            // model's value at a point `f(t⃗)` that occurs NOWHERE in
                            // the ground assertions is a model-COMPLETION artifact:
                            // EUF/LIA hand out a fabricated default (measured: the
                            // model returns `0` for `(wrapping_add 256 200)`, a term
                            // no assertion mentions). Nothing constrains `f` there, so
                            // the "counterexample" refutes nothing — yet MBQI adds the
                            // instance, and that instance's own head `f(t⃗)` becomes a
                            // NEW ground term, hence a new candidate, whose instance
                            // creates a deeper term... the matching loop. Measured on
                            // ay #7883's `wrapping_add` definition: round 0 added 3
                            // such instances, round 1 then added 265, and the 265-mod
                            // ground re-solve does not return (>70s standalone) — the
                            // 30s timeout.
                            //
                            // At a point that DOES occur, the model value is pinned by
                            // the assertions and the instance is a genuine refutation
                            // step, so it is still added: E-matching's own instances
                            // (and any earlier MBQI instance) put exactly those points
                            // in `occurring_ground`.
                            //
                            // SOUNDNESS: skipping only ever WITHHOLDS a valid ground
                            // consequence, so it cannot manufacture UNSAT; and the skip
                            // clears `all_satisfied`, so the SAT leg below can never
                            // claim "verified at every candidate" on the strength of a
                            // point we declined to check. Worst case is a lost
                            // refutation, i.e. `Unknown` — never a wrong verdict.
                            let phantom = match definition_head {
                                Some(head) => {
                                    let head_ground =
                                        subst_vars(&mut self.ctx.terms, head, &subst_map);
                                    !occurring_ground.contains(&head_ground)
                                }
                                None => false,
                            };
                            if !phantom && seen_instantiations.insert(ground_body) {
                                new_instantiations.push(ground_body);
                            }
                            quant_all_true = false;
                            all_satisfied = false;
                            // Continue checking — multiple counterexamples per round
                            // help convergence.
                        }
                        _ => {
                            match self.quantifier_instance_uf_completion_eval_for_quantifier(
                                ground_body,
                                &vars,
                                body,
                            ) {
                                UfCompletionEval::True => {}
                                UfCompletionEval::False => {
                                    if seen_instantiations.insert(ground_body) {
                                        new_instantiations.push(ground_body);
                                    }
                                    quant_all_true = false;
                                    all_satisfied = false;
                                }
                                UfCompletionEval::Unknown => {
                                    // SPECIAL-RELATIONS SAT-CERTIFICATION
                                    // (#special-relations-mbqi-sat).
                                    //
                                    // A lone universal over an uninterpreted sort
                                    // (Z3's order axioms `forall x. R(x,x)`,
                                    // `forall x,y. R(x,y) & R(y,x) => x=y`, ...)
                                    // leaves the predicate `R` UNDEFINED at ground
                                    // points the candidate model never had to touch
                                    // (`R(a,a)`, `R(b,b)`), so model evaluation is
                                    // `Unknown` and `all_satisfied` never turns true —
                                    // MBQI falls to `Unknown(QuantifierUnhandled)` even
                                    // though the constraint is genuinely SAT.
                                    //
                                    // When the instance introduces NO new domain
                                    // element of the finite uninterpreted binder
                                    // universe, add it as a lemma to PIN the predicate
                                    // at that point. Re-solving then assigns those
                                    // atoms a concrete Bool over the fixed constant
                                    // universe, and the next round's quick-check
                                    // re-confirms every instance → genuine SAT.
                                    if self.mbqi_ground_instance_pins_finite_universe(
                                        &vars,
                                        ground_body,
                                        &ground_by_sort,
                                    ) && seen_instantiations.insert(ground_body)
                                    {
                                        new_instantiations.push(ground_body);
                                    }
                                    // Unknown — can't determine yet. Mark incomplete but
                                    // continue trying other substitutions.
                                    quant_all_true = false;
                                    all_satisfied = false;
                                }
                            }
                        }
                    }

                    checked += 1;

                    // Advance to next combination.
                    let mut carry = true;
                    for i in (0..vars.len()).rev() {
                        if carry {
                            indices[i] += 1;
                            if indices[i] < candidates_per_var[i].len() {
                                carry = false;
                            } else {
                                indices[i] = 0;
                            }
                        }
                    }
                    if carry {
                        break; // All combinations exhausted.
                    }
                }

                let _ = quant_all_true;
            }

            if new_instantiations.is_empty() {
                if all_satisfied {
                    // Every quantifier body is true under the model for all checked
                    // ground substitutions. The SAT result is genuine (modulo
                    // completeness of the ground term set).
                    return Some(Ok(SolveResult::Sat));
                }
                // No counterexamples found but not all satisfied (evaluation was
                // Unknown or budget hit). MBQI is incomplete.
                break;
            }

            // Add counterexample instantiations to assertions and re-solve.
            for inst in &new_instantiations {
                self.ctx.assertions.push(*inst);
            }

            let re_result = self.solve_for_category(category);
            match re_result {
                Ok(SolveResult::Sat) => {
                    // Still SAT with new lemmas. Next round will re-check with
                    // the updated model.
                    continue;
                }
                Ok(SolveResult::Unsat(_)) => {
                    // The counterexample instantiations made the problem UNSAT.
                    // This is genuine: the quantifiers were violated.
                    return Some(Ok(SolveResult::unsat()));
                }
                other => {
                    return Some(other);
                }
            }
        }

        // MBQI did not find definitive result. Return None to let caller
        // fall back to Unknown.
        None
    }

    /// Quick-check skipped `forall` assertions against the restored model.
    ///
    /// This is a soundness gate for the SAT-validation path: when
    /// `finalize_sat_model_validation` had to skip one or more quantified
    /// assertions, independent evidence on other assertions is not enough to
    /// trust SAT. We re-run the MBQI quick-check over the restored original
    /// assertions and degrade to `Unknown` if:
    /// - some substitution falsifies a skipped `forall`, or
    /// - the gate cannot conclusively evaluate the quantifier space
    ///   (empty candidates, unknown evaluation, or budget exhaustion).
    ///
    /// Unlike full MBQI refinement, this gate combines existing ground terms
    /// with synthesized canonical witnesses for every bound-variable sort.
    /// That lets it probe candidates that E-matching never produced, such as
    /// the const-zero array witness in Z3 #6303 / ay #8803.
    pub(in crate::executor) fn mbqi_soundness_gate_for_skipped_quantifiers(
        &mut self,
    ) -> SkippedQuantifierMbqiGate {
        let has_any_quantifier = self
            .ctx
            .assertions
            .iter()
            .copied()
            .any(|a| contains_quantifier(&self.ctx.terms, a));
        let forall_quants: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();

        if forall_quants.is_empty() {
            return if has_any_quantifier {
                // A quantifier nested under Boolean structure is not a direct
                // asserted forall and cannot be validated by this root-only
                // enumerator.
                SkippedQuantifierMbqiGate::Inconclusive
            } else {
                SkippedQuantifierMbqiGate::NoQuantifiers
            };
        }
        if self.ctx.assertions.iter().copied().any(|assertion| {
            contains_quantifier(&self.ctx.terms, assertion)
                && !matches!(self.ctx.terms.get(assertion), TermData::Forall(..))
        }) || forall_quants.iter().copied().any(|quant| {
            matches!(self.ctx.terms.get(quant), TermData::Forall(_, body, _)
                if contains_quantifier(&self.ctx.terms, *body))
        }) {
            return SkippedQuantifierMbqiGate::Inconclusive;
        }

        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, &self.ctx.assertions);

        let all_bound_sorts: HashSet<Sort> = forall_quants
            .iter()
            .filter_map(|&q| match self.ctx.terms.get(q) {
                TermData::Forall(vars, _, _) => Some(vars.clone()),
                _ => None,
            })
            .flatten()
            .map(|(_, sort)| sort)
            .collect();

        let synthesized = if all_bound_sorts.is_empty() {
            HashMap::default()
        } else {
            self.synthesize_mbqi_candidates(&all_bound_sorts)
        };

        let mut incomplete = false;
        let mut all_domains_exhaustive = true;

        for &quant in &forall_quants {
            let (vars, body) = match self.ctx.terms.get(quant) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => continue,
            };

            if vars.is_empty() {
                let eval = if let Some(ref model) = self.last_model {
                    self.evaluate_term(model, body)
                } else {
                    EvalValue::Unknown
                };
                match eval {
                    EvalValue::Bool(true) => continue,
                    EvalValue::Bool(false) => {
                        return SkippedQuantifierMbqiGate::Inconclusive;
                    }
                    _ => {
                        incomplete = true;
                        continue;
                    }
                }
            }

            // Bool is the only domain this quick checker enumerates in full:
            // synthesis always supplies both truth values.  Int, Real, String,
            // arrays, and model-provided uninterpreted universes are samples;
            // BitVec synthesis likewise supplies only zero plus observed model
            // values.  Their all-true result must remain inconclusive.  The
            // dedicated EPR/finite-table certificates handle their separately
            // proved finite cases.
            all_domains_exhaustive &= vars.iter().all(|(_, sort)| matches!(sort, Sort::Bool));

            let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
            let mut any_empty = false;
            for (_name, sort) in &vars {
                let mut seen: HashSet<TermId> = HashSet::default();
                let mut candidates: Vec<TermId> = Vec::new();
                for &t in ground_by_sort.get(sort).into_iter().flatten() {
                    if seen.insert(t) {
                        candidates.push(t);
                    }
                }
                for &t in synthesized.get(sort).into_iter().flatten() {
                    if seen.insert(t) {
                        candidates.push(t);
                    }
                }
                if candidates.is_empty() {
                    any_empty = true;
                    break;
                }
                candidates_per_var.push(candidates);
            }
            if any_empty {
                incomplete = true;
                continue;
            }

            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let mut indices: Vec<usize> = vec![0; vars.len()];
            let mut checked = 0usize;

            loop {
                if checked >= MAX_QUICK_CHECK_CANDIDATES {
                    incomplete = true;
                    break;
                }

                let binding: Vec<TermId> = indices
                    .iter()
                    .enumerate()
                    .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
                    .collect();

                let subst_map: HashMap<String, TermId> = var_names
                    .iter()
                    .zip(binding.iter())
                    .map(|(name, &t)| (name.clone(), t))
                    .collect();
                let ground_body = subst_vars(&mut self.ctx.terms, body, &subst_map);

                let eval = if let Some(ref model) = self.last_model {
                    self.evaluate_term(model, ground_body)
                } else {
                    EvalValue::Unknown
                };

                match eval {
                    EvalValue::Bool(true) => {}
                    EvalValue::Bool(false) => {
                        return SkippedQuantifierMbqiGate::Inconclusive;
                    }
                    _ => match self.quantifier_instance_uf_completion_eval_for_quantifier(
                        ground_body,
                        &vars,
                        body,
                    ) {
                        UfCompletionEval::True => {}
                        UfCompletionEval::False => {
                            return SkippedQuantifierMbqiGate::Inconclusive;
                        }
                        UfCompletionEval::Unknown => {
                            incomplete = true;
                        }
                    },
                }

                checked += 1;

                let mut carry = true;
                for i in (0..vars.len()).rev() {
                    if carry {
                        indices[i] += 1;
                        if indices[i] < candidates_per_var[i].len() {
                            carry = false;
                        } else {
                            indices[i] = 0;
                        }
                    }
                }
                if carry {
                    break;
                }
            }
        }

        if incomplete || !all_domains_exhaustive {
            SkippedQuantifierMbqiGate::Inconclusive
        } else {
            SkippedQuantifierMbqiGate::ExhaustivelySatisfied
        }
    }

    fn quantifier_instance_uf_completion_eval_for_quantifier(
        &self,
        ground_instance: TermId,
        _vars: &[(String, Sort)],
        _body: TermId,
    ) -> UfCompletionEval {
        if self.assertions_force_false(ground_instance) {
            return UfCompletionEval::False;
        }
        // A syntactic UF/sequence "completion" shape is not evidence that this
        // instance is true in the candidate model. Different accepted atoms may
        // require incompatible interpretations, and an E-matched point does not
        // establish a total function. Only a model-independent propositional
        // tautology may turn an unevaluable instance into `True` here. All other
        // unevaluable shapes fail closed; independently constructed total-model
        // certificates run later in result mapping.
        if self.ground_body_is_propositional_tautology(ground_instance) {
            UfCompletionEval::True
        } else {
            UfCompletionEval::Unknown
        }
    }

    /// Sound MBQI completeness helper: decide whether a ground quantifier
    /// instance is a *propositional tautology* — true under EVERY truth
    /// assignment to its non-Boolean-structural atoms.
    ///
    /// When the candidate model cannot evaluate a ground instance (e.g. the
    /// body mentions an uninterpreted predicate over a synthesized universe
    /// element that the model never constrained), the model evaluation returns
    /// `Unknown`. But many such instances are valid regardless of the model:
    /// `(=> (p e) (p e))` desugars to `(or (p e) (not (p e)))`, which is
    /// `phi \/ ~phi` — true no matter how the model interprets `p(e)`. The
    /// classic MBQI SAT shape `forall x,y. p(x,y) => p(y,x)` over an empty
    /// universe yields exactly this instance.
    ///
    /// We treat each maximal non-Boolean-connective subterm of Boolean sort as
    /// an opaque propositional atom, collect the distinct atoms, and (when the
    /// atom count is small enough to enumerate exhaustively) check that the
    /// formula evaluates to `true` under all 2^n assignments. If so it is a
    /// tautology and holds in every model extension.
    ///
    /// SOUNDNESS: this can only ever return `true` for a genuine tautology, so
    /// it can only upgrade an `Unknown` instance to `True`. It NEVER reports a
    /// counterexample and NEVER claims `False`, so it cannot cause a wrong-unsat
    /// nor mask a real counterexample (a non-tautology returns `false` here and
    /// the instance stays `Unknown`, keeping MBQI fail-closed). The enumeration
    /// is exact for the bounded atom count; above the bound we conservatively
    /// return `false` (stay `Unknown`).
    fn ground_body_is_propositional_tautology(&self, term: TermId) -> bool {
        /// Max distinct propositional atoms to enumerate exhaustively (2^n).
        const MAX_PROP_ATOMS: usize = 16;

        if self.ctx.terms.sort(term) != &Sort::Bool {
            return false;
        }

        // Collect distinct atoms (maximal Boolean subterms that are NOT
        // Boolean connectives). Determinism is not required for correctness;
        // we only need the *set* of atoms and a stable index per atom.
        let mut atoms: Vec<TermId> = Vec::new();
        let mut atom_index: HashMap<TermId, usize> = HashMap::default();
        if !self.collect_prop_atoms(term, &mut atoms, &mut atom_index, MAX_PROP_ATOMS) {
            // Too many atoms (or a structural form we don't model) — bail out
            // soundly to "not a known tautology".
            return false;
        }

        let n = atoms.len();
        if n == 0 {
            // No atoms: the formula is a constant Boolean expression. Evaluate
            // it under the (irrelevant) empty assignment.
            return self.eval_prop_under_assignment(term, &atom_index, 0) == Some(true);
        }

        // Enumerate all 2^n assignments; tautology iff true under every one.
        let total: u64 = 1u64 << n;
        for assignment in 0..total {
            match self.eval_prop_under_assignment(term, &atom_index, assignment) {
                Some(true) => {}
                // Falsified by some assignment, or could not be reduced to a
                // pure-propositional value — not a (recognizable) tautology.
                _ => return false,
            }
        }
        true
    }

    /// Recursively collect propositional atoms of a Boolean term, descending
    /// only through Boolean connectives (`not`, `and`, `or`, `=>`, `xor`,
    /// Boolean `=`/`distinct`, `ite` with a Boolean condition+branches, and the
    /// dedicated `Not`/`Ite` term nodes). Anything else of Boolean sort is an
    /// opaque atom. Returns `false` if the distinct atom count would exceed
    /// `max_atoms` (caller treats this as "give up").
    fn collect_prop_atoms(
        &self,
        term: TermId,
        atoms: &mut Vec<TermId>,
        atom_index: &mut HashMap<TermId, usize>,
        max_atoms: usize,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(_)) => true,
            TermData::Not(inner) => self.collect_prop_atoms(*inner, atoms, atom_index, max_atoms),
            TermData::Ite(c, t, e)
                if self.ctx.terms.sort(*t) == &Sort::Bool
                    && self.ctx.terms.sort(*e) == &Sort::Bool =>
            {
                self.collect_prop_atoms(*c, atoms, atom_index, max_atoms)
                    && self.collect_prop_atoms(*t, atoms, atom_index, max_atoms)
                    && self.collect_prop_atoms(*e, atoms, atom_index, max_atoms)
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                let is_bool_connective = match name {
                    "and" | "or" | "=>" | "xor" | "not" => true,
                    // `=` / `distinct` are Boolean connectives only when their
                    // operands are themselves Boolean (iff / xor). Otherwise the
                    // whole `=` application is an opaque Boolean atom.
                    "=" | "distinct" => args.iter().all(|&a| self.ctx.terms.sort(a) == &Sort::Bool),
                    "ite" => {
                        args.len() == 3
                            && self.ctx.terms.sort(args[1]) == &Sort::Bool
                            && self.ctx.terms.sort(args[2]) == &Sort::Bool
                    }
                    _ => false,
                };
                if is_bool_connective {
                    for &arg in args {
                        if !self.collect_prop_atoms(arg, atoms, atom_index, max_atoms) {
                            return false;
                        }
                    }
                    true
                } else {
                    self.register_atom(term, atoms, atom_index, max_atoms)
                }
            }
            // Var/Const(non-bool)/other Boolean-sorted leaves: opaque atom.
            _ => self.register_atom(term, atoms, atom_index, max_atoms),
        }
    }

    fn register_atom(
        &self,
        term: TermId,
        atoms: &mut Vec<TermId>,
        atom_index: &mut HashMap<TermId, usize>,
        max_atoms: usize,
    ) -> bool {
        if atom_index.contains_key(&term) {
            return true;
        }
        if atoms.len() >= max_atoms {
            return false;
        }
        let idx = atoms.len();
        atoms.push(term);
        atom_index.insert(term, idx);
        true
    }

    /// Evaluate a propositional formula under a bitmask assignment to its atoms
    /// (`assignment >> atom_index(atom) & 1`). Returns `None` if a subterm is
    /// neither a recognized Boolean connective nor a registered atom (should not
    /// happen after a successful `collect_prop_atoms`, but we fail closed).
    fn eval_prop_under_assignment(
        &self,
        term: TermId,
        atom_index: &HashMap<TermId, usize>,
        assignment: u64,
    ) -> Option<bool> {
        if let Some(&idx) = atom_index.get(&term) {
            return Some((assignment >> idx) & 1 == 1);
        }
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            TermData::Not(inner) => self
                .eval_prop_under_assignment(*inner, atom_index, assignment)
                .map(|v| !v),
            TermData::Ite(c, t, e) => {
                let cv = self.eval_prop_under_assignment(*c, atom_index, assignment)?;
                if cv {
                    self.eval_prop_under_assignment(*t, atom_index, assignment)
                } else {
                    self.eval_prop_under_assignment(*e, atom_index, assignment)
                }
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                match name {
                    "and" => {
                        let mut acc = true;
                        for &a in args {
                            acc &= self.eval_prop_under_assignment(a, atom_index, assignment)?;
                        }
                        Some(acc)
                    }
                    "or" => {
                        let mut acc = false;
                        for &a in args {
                            acc |= self.eval_prop_under_assignment(a, atom_index, assignment)?;
                        }
                        Some(acc)
                    }
                    "not" if args.len() == 1 => self
                        .eval_prop_under_assignment(args[0], atom_index, assignment)
                        .map(|v| !v),
                    "=>" if !args.is_empty() => {
                        // (=> a b c ... z) == (or (not a) (not b) ... z)
                        let last = *args.last().unwrap();
                        for &a in &args[..args.len() - 1] {
                            if !self.eval_prop_under_assignment(a, atom_index, assignment)? {
                                return Some(true);
                            }
                        }
                        self.eval_prop_under_assignment(last, atom_index, assignment)
                    }
                    "xor" => {
                        let mut acc = false;
                        for &a in args {
                            acc ^= self.eval_prop_under_assignment(a, atom_index, assignment)?;
                        }
                        Some(acc)
                    }
                    "=" if args.len() >= 2
                        && args.iter().all(|&a| self.ctx.terms.sort(a) == &Sort::Bool) =>
                    {
                        let first =
                            self.eval_prop_under_assignment(args[0], atom_index, assignment)?;
                        for &a in &args[1..] {
                            if self.eval_prop_under_assignment(a, atom_index, assignment)? != first
                            {
                                return Some(false);
                            }
                        }
                        Some(true)
                    }
                    "distinct"
                        if args.len() == 2
                            && args.iter().all(|&a| self.ctx.terms.sort(a) == &Sort::Bool) =>
                    {
                        let a0 =
                            self.eval_prop_under_assignment(args[0], atom_index, assignment)?;
                        let a1 =
                            self.eval_prop_under_assignment(args[1], atom_index, assignment)?;
                        Some(a0 != a1)
                    }
                    "ite" if args.len() == 3 => {
                        let cv =
                            self.eval_prop_under_assignment(args[0], atom_index, assignment)?;
                        if cv {
                            self.eval_prop_under_assignment(args[1], atom_index, assignment)
                        } else {
                            self.eval_prop_under_assignment(args[2], atom_index, assignment)
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(in crate::executor) fn assertions_force_false(&self, term: TermId) -> bool {
        let facts = self.asserted_conjunct_facts();
        self.facts_force_false(term, &facts)
    }

    pub(in crate::executor) fn assertion_window_has_completion_forced_false(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let facts = self.assertion_window_conjunct_facts(assertions);
        assertions
            .iter()
            .copied()
            .any(|assertion| self.facts_force_false(assertion, &facts))
    }

    fn asserted_conjunct_facts(&self) -> HashSet<TermId> {
        self.assertion_window_conjunct_facts(&self.ctx.assertions)
    }

    fn assertion_window_conjunct_facts(&self, assertions: &[TermId]) -> HashSet<TermId> {
        let mut facts = HashSet::default();
        for &assertion in assertions {
            self.collect_asserted_conjunct_facts(assertion, &mut facts);
        }
        facts
    }

    fn collect_asserted_conjunct_facts(&self, term: TermId, facts: &mut HashSet<TermId>) {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            facts.insert(term);
            return;
        };
        if sym.name() == "and" {
            for &arg in args {
                self.collect_asserted_conjunct_facts(arg, facts);
            }
        } else {
            facts.insert(term);
        }
    }

    fn facts_force_false(&self, term: TermId, facts: &HashSet<TermId>) -> bool {
        if self.quantifier_consumer_seq_elem_injectivity_forced_false(term) {
            return true;
        }
        if facts
            .iter()
            .copied()
            .any(|fact| self.term_is_negation_of(fact, term))
        {
            return true;
        }
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => self.facts_imply_true(*inner, facts),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => {
                self.facts_imply_true(args[0], facts)
            }
            TermData::App(sym, args) if sym.name() == "or" => args
                .iter()
                .copied()
                .all(|arg| self.facts_force_false(arg, facts)),
            TermData::App(sym, args) if sym.name() == "and" => args
                .iter()
                .copied()
                .any(|arg| self.facts_force_false(arg, facts)),
            _ => false,
        }
    }

    fn facts_imply_true(&self, term: TermId, facts: &HashSet<TermId>) -> bool {
        if facts.contains(&term) {
            return true;
        }
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => *value,
            TermData::Not(inner) => self.facts_force_false(*inner, facts),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => {
                self.facts_force_false(args[0], facts)
            }
            TermData::App(sym, args) if sym.name() == "and" => args
                .iter()
                .copied()
                .all(|arg| self.facts_imply_true(arg, facts)),
            TermData::App(sym, args) if sym.name() == "or" => args
                .iter()
                .copied()
                .any(|arg| self.facts_imply_true(arg, facts)),
            TermData::App(sym, args) if matches!(sym.name(), "<=" | "<") && args.len() == 2 => {
                self.facts_imply_int_upper_bound(sym.name(), args[0], args[1], facts)
            }
            _ => false,
        }
    }

    fn term_is_negation_of(&self, maybe_negation: TermId, positive: TermId) -> bool {
        match self.ctx.terms.get(maybe_negation) {
            TermData::Not(inner) => *inner == positive,
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => {
                args[0] == positive
            }
            _ => false,
        }
    }

    fn facts_imply_int_upper_bound(
        &self,
        target_op: &str,
        target_lhs: TermId,
        target_rhs: TermId,
        facts: &HashSet<TermId>,
    ) -> bool {
        for &fact in facts {
            let TermData::App(sym, args) = self.ctx.terms.get(fact) else {
                continue;
            };
            if args.len() != 2 || sym.name() != "<=" || args[1] != target_rhs {
                continue;
            }
            if args[0] == target_lhs && target_op == "<=" {
                return true;
            }
            let Some(offset) = self.facts_equate_to_base_plus_offset(args[0], target_lhs, facts)
            else {
                continue;
            };
            if target_op == "<=" && offset >= num_bigint::BigInt::ZERO {
                return true;
            }
            if target_op == "<" && offset > num_bigint::BigInt::ZERO {
                return true;
            }
        }
        false
    }

    fn facts_equate_to_base_plus_offset(
        &self,
        shifted: TermId,
        base: TermId,
        facts: &HashSet<TermId>,
    ) -> Option<num_bigint::BigInt> {
        for &fact in facts {
            let TermData::App(sym, args) = self.ctx.terms.get(fact) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            if args[0] == shifted {
                if let Some(offset) = self.term_base_plus_offset(args[1], base) {
                    return Some(offset);
                }
            }
            if args[1] == shifted {
                if let Some(offset) = self.term_base_plus_offset(args[0], base) {
                    return Some(offset);
                }
            }
        }
        None
    }

    fn term_base_plus_offset(&self, term: TermId, base: TermId) -> Option<num_bigint::BigInt> {
        if term == base {
            return Some(num_bigint::BigInt::ZERO);
        }
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "+" || args.len() != 2 {
            return None;
        }
        if args[0] == base {
            return self.int_constant_value(args[1]);
        }
        if args[1] == base {
            return self.int_constant_value(args[0]);
        }
        None
    }

    fn int_constant_value(&self, term: TermId) -> Option<num_bigint::BigInt> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Int(value)) => Some(value.clone()),
            _ => None,
        }
    }

    pub(in crate::executor) fn quantifier_supported_by_uf_completion(&self, quant: TermId) -> bool {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return false;
        };
        // SOUNDNESS (#forall-int-uf-completion wrong-sat): a `forall` whose body
        // is PURE arithmetic/boolean — every operator is a builtin LIA/LRA/Bool
        // symbol applied to variables and constants, with NO uninterpreted
        // function, array, datatype, sequence, string, or FP application — has
        // nothing for UF completion to complete: there is no uninterpreted
        // symbol whose interpretation a model could freely choose per
        // instantiation. Certifying such a `forall` as completion-safe is
        // unsound. Example: `(forall ((q0 Int)) (=> (> q0 3) (<= q0 c0)))` is a
        // genuine arithmetic universal (UNSAT — q0 is unbounded above so the
        // consequent must eventually fail), but `quantifier_consumer_or_has_simple_
        // satisfiable_branch` accepts the consistent branch `(<= q0 c0)` and the
        // gate would report a wrong SAT. Pure-arithmetic universals must be
        // discharged by the arithmetic quantifier procedures (CEGQI/MBQI), not
        // UF completion, so decline the certificate here and let them through.
        //
        // An uninterpreted/theory application is treated as an opaque CONSTANT
        // when its arguments do not mention the bound variables (e.g. `(f q0)`
        // for an outer-quantified `q0` while reasoning about `(forall q1 ...)`):
        // from this `forall`'s view it is a fixed value, so a body that is pure
        // arithmetic in the bound variables modulo such constants is still a
        // genuine arithmetic universal with no UF-of-bound-var for completion to
        // complete. Example: `(forall q1 (=> (<= (+ q1 3) -2) (< (f q0) q1)))`
        // is UNSAT (q1 is unbounded below), but uf completion would report SAT.
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        if self.body_is_pure_arith_bool(*body, &bound) {
            return false;
        }
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/quant: term_supported={} const_def={} uf_def={}",
                self.term_supported_by_uf_completion(*body),
                self.quantifier_is_constant_uf_definition(vars, *body),
                self.quantifier_is_uf_definition(vars, *body),
            );
        }
        self.term_supported_by_uf_completion(*body)
            || self.quantifier_is_constant_uf_definition(vars, *body)
            || self.quantifier_is_uf_definition(vars, *body)
    }

    /// True when `term` mentions only builtin arithmetic / boolean operators
    /// over variables and constants — i.e. it contains NO uninterpreted
    /// function, array, datatype, sequence, string, or FP application. Such a
    /// term exposes no symbol whose interpretation UF completion could choose,
    /// so a `forall` with a pure-arith/bool body is never a UF completion.
    ///
    /// `=`/`distinct` and the arithmetic comparisons are builtin, but the
    /// recursion descends into their arguments: `(= (f x) 3)` is NOT pure
    /// because `(f x)` is an uninterpreted application, whereas `(= q0 c0)`
    /// (variable vs constant) is. A nested quantifier or `let` is treated as
    /// non-pure (return `false`) so the certificate is only ever *declined* by
    /// this guard, never granted.
    fn body_is_pure_arith_bool(&self, term: TermId, bound: &HashSet<String>) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) => true,
            // A variable of an interpreted sort (Int/Real/Bool/BitVec/...) is
            // genuine pure-arith/bool structure. A variable of a *freely
            // collapsible* uninterpreted (non-datatype) sort is NOT: `(= u v)`
            // between two such variables is exactly what UF completion may
            // satisfy by shrinking the sort's domain to a singleton, so a body
            // that is `(= u v)` over an uninterpreted sort is a legitimate
            // completion (`same_sort_variable_equality`), not a pure-arith
            // universal. Classifying it as pure would wrongly DECLINE that sound
            // certificate and degrade `(forall ((u U) (v U)) (= u v))` to
            // Unknown. Interpreted-sort and datatype-sort variables stay pure
            // here, so the arithmetic/BV wrong-SAT guard is unchanged.
            TermData::Var(_, _) => {
                let sort = self.ctx.terms.sort(term);
                // Pure iff NOT a freely-collapsible uninterpreted sort: an
                // interpreted sort, or a datatype sort (whose constructors are
                // fixed), stays pure.
                !matches!(sort, Sort::Uninterpreted(_)) || self.binder_sort_is_datatype(sort)
            }
            TermData::Not(inner) => self.body_is_pure_arith_bool(*inner, bound),
            TermData::Ite(cond, then_term, else_term) => {
                self.body_is_pure_arith_bool(*cond, bound)
                    && self.body_is_pure_arith_bool(*then_term, bound)
                    && self.body_is_pure_arith_bool(*else_term, bound)
            }
            TermData::App(sym, args)
                if is_pure_arith_bool_symbol(sym.name())
                    || is_interpreted_bv_symbol(sym.name()) =>
            {
                // Interpreted BitVector operators are closed-form theory functions
                // with no interpretation for UF completion to choose, so a forall
                // body built only from them over (bound) variables and constants is
                // a genuine BV universal — decline the UF-completion certificate and
                // let the BV quantifier procedure (bv_mbqi exhaustive / fail-closed)
                // decide it, instead of granting a heuristic SAT (#bv-quant-WS).
                args.iter()
                    .copied()
                    .all(|a| self.body_is_pure_arith_bool(a, bound))
            }
            // A non-builtin (uninterpreted / array / datatype / seq / string / FP)
            // application that does NOT mention a bound variable is an opaque
            // CONSTANT from this `forall`'s perspective — pure-arith-compatible.
            // One that DOES mention a bound variable is a genuine UF-of-bound-var,
            // so the body is not pure arithmetic and the completion check stands.
            TermData::App(_, _) => !self.term_contains_bound_var(term, bound),
            _ => false,
        }
    }

    /// True when `sort` is a user-declared datatype, including one surfaced as
    /// `Sort::Uninterpreted(name)` by `declare-datatype`. MBQI cannot synthesize
    /// witnesses of a datatype sort and finite-domain expansion does not
    /// enumerate its constructors, so a `forall` over it is not soundly
    /// dischargeable by the ground/E-matching path or by UF completion.
    pub(in crate::executor) fn binder_sort_is_datatype(&self, sort: &Sort) -> bool {
        let name = match sort {
            Sort::Datatype(_) => return true,
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return false,
        };
        self.ctx.datatype_iter().any(|(dt_name, _)| dt_name == name)
    }

    pub(in crate::executor) fn term_supported_by_uf_completion(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(true)) => true,
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                self.equality_supported_by_uf_completion(args[0], args[1])
                    || self.equality_supported_by_uf_completion(args[1], args[0])
                    || self.same_sort_variable_equality(args[0], args[1])
                    || self.uf_definition_supported_by_completion(args[0], args[1])
                    || self.uf_definition_supported_by_completion(args[1], args[0])
                    || self.quantifier_consumer_seq_index_restore_bridge_equality(args[0], args[1])
                    || self.quantifier_consumer_seq_index_restore_bridge_equality(args[1], args[0])
                    || self.quantifier_consumer_view_variable_alias_equality(args[0], args[1])
            }
            TermData::App(sym, args)
                if self.is_quantifier_consumer_option_membership_axiom_body(sym.name(), args) =>
            {
                true
            }
            TermData::Not(inner)
                if self.is_quantifier_consumer_option_none_some_disequality(*inner) =>
            {
                true
            }
            TermData::Not(inner)
                if self.is_quantifier_consumer_seq_empty_contains_instance(*inner) =>
            {
                true
            }
            TermData::App(sym, args)
                if sym.name() == "<="
                    && self.is_quantifier_consumer_seq_len_nonnegative_instance(args) =>
            {
                true
            }
            TermData::App(sym, args)
                if matches!(sym.name(), "<" | "<=")
                    && self.is_quantifier_consumer_seq_len_proxy_lower_bound(args) =>
            {
                true
            }
            TermData::App(sym, args)
                if sym.name() == "or"
                    && self.is_quantifier_consumer_seq_elem_injectivity_instance(args) =>
            {
                true
            }
            TermData::App(sym, args)
                if sym.name() == "or"
                    && self.is_quantifier_consumer_seq_get_in_bounds_instance(args) =>
            {
                true
            }
            TermData::App(sym, args)
                if sym.name() == "or"
                    && self.is_quantifier_consumer_bucket_guarded_frame_clause(args) =>
            {
                true
            }
            TermData::App(sym, args)
                if sym.name() == "or"
                    && self.quantifier_consumer_or_has_simple_satisfiable_branch(args) =>
            {
                true
            }
            TermData::App(sym, args) if self.is_true_datatype_tester_instance(sym.name(), args) => {
                true
            }
            TermData::App(sym, args)
                if self.is_single_constructor_datatype_tester_instance(sym.name(), args) =>
            {
                true
            }
            TermData::App(sym, args) if sym.name() == "or" && !args.is_empty() => args
                .iter()
                .copied()
                .any(|arg| self.term_supported_by_uf_completion(arg)),
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_by_uf_completion(arg)),
            TermData::App(sym, _args)
                if is_quantifier_consumer_completable_bool_predicate(sym.name()) =>
            {
                true
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_uf_definition_condition(*cond)
                    && self.term_supported_by_uf_completion(*then_term)
                    && self.term_supported_by_uf_completion(*else_term)
            }
            _ => false,
        }
    }

    /// True when `term` contains (anywhere in its subtree) an application of a
    /// COMPLETABLE uninterpreted-function symbol — one whose value the quantifier_consumer /
    /// mod-div completion path is free to choose to satisfy a constraint.
    ///
    /// Pure interpreted arithmetic / boolean structure (`+ - * div mod abs`,
    /// comparisons, connectives, constants, free arithmetic variables) provides
    /// NO such freedom, so an atom built only from it is a hard constraint the
    /// real solver must decide rather than something the completion can arrange.
    /// Used to gate the arithmetic-atom arms of the *_supported_by_completion
    /// predicates so they cannot certify an UNSAT ground arithmetic atom as
    /// "supported" and let the SAT shortcut accept it with an empty model
    /// (#quantifier_consumer-arith).
    pub(in crate::executor) fn term_mentions_completable_uf(&self, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // An applied symbol that is neither an interpreted
                    // arithmetic/array operator nor a logical connective is a
                    // completable UF (matches the symbol set the completion can
                    // assign values to). `is_mbqi_completable_uf_symbol`
                    // excludes the interpreted operators and theory ops.
                    if is_mbqi_completable_uf_symbol(name) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        }
        false
    }

    pub(in crate::executor) fn quantifier_consumer_ground_assertion_supported_by_completion(
        &self,
        term: TermId,
    ) -> bool {
        self.quantifier_consumer_ground_assertion_supported_by_completion_ext(term, false)
    }

    /// `model_backed` relaxes the #quantifier_consumer-arith per-atom freedom gate back to
    /// the evaluability-only (pre-gate) semantics. It is sound ONLY when the
    /// ground solver actually produced (and, downstream, validated) a genuine
    /// SAT model for the ground assertions: in that case every pure-arithmetic
    /// atom's truth is established by the model itself and needs no completion
    /// freedom. It must stay `false` on any path that can promote a lower
    /// `Unknown` (e.g. mod/div incompleteness with an empty model) to SAT on
    /// the strength of this certificate alone — that is exactly the
    /// #quantifier_consumer-arith wrong-SAT.
    pub(in crate::executor) fn quantifier_consumer_ground_assertion_supported_by_completion_ext(
        &self,
        term: TermId,
        model_backed: bool,
    ) -> bool {
        if self.term_supported_by_uf_completion(term) {
            return true;
        }
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(true)) => true,
            TermData::Var(_, _) if self.ctx.terms.sort(term) == &Sort::Bool => true,
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or" | "=>" | "xor") => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_condition_ext(arg, model_backed)),
            // Arithmetic equality / comparison atoms are "supported by
            // completion" only when at least one operand mentions a COMPLETABLE
            // UF symbol whose value the completion is free to choose. A PURE
            // interpreted-arithmetic atom (constants + free arithmetic vars
            // combined through +,-,*,div,mod,abs,...) has no such freedom: it is
            // a hard arithmetic constraint that the arithmetic solver must
            // decide. Claiming it "supported" here let the quantifier_consumer/mod-div SAT
            // shortcut accept an UNSAT ground atom such as
            // `(> (mod (mod x0 5) 3) (abs (+ -5 x0)))` with an empty model
            // (wrong SAT). Without a completable UF the empty model cannot
            // satisfy it, so decline and let the real solver decide (#quantifier_consumer-arith).
            // With `model_backed` (a genuine validated ground model exists) the
            // atom's truth is already established, so evaluability suffices.
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed))
                    && (model_backed
                        || args
                            .iter()
                            .copied()
                            .any(|arg| self.term_mentions_completable_uf(arg)))
            }
            TermData::App(sym, args) if matches!(sym.name(), "<" | "<=" | ">" | ">=") => {
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed))
                    && (model_backed
                        || args
                            .iter()
                            .copied()
                            .any(|arg| self.term_mentions_completable_uf(arg)))
            }
            TermData::Not(inner) => {
                self.term_supported_as_uf_definition_condition_ext(*inner, model_backed)
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_uf_definition_condition_ext(*cond, model_backed)
                    && self.term_supported_as_uf_definition_condition_ext(*then_term, model_backed)
                    && self.term_supported_as_uf_definition_condition_ext(*else_term, model_backed)
            }
            _ => false,
        }
    }

    fn is_quantifier_consumer_option_membership_axiom_body(
        &self,
        name: &str,
        args: &[TermId],
    ) -> bool {
        if name != "__quantifier_consumer_is_option" || args.len() != 1 {
            return false;
        }
        matches!(self.ctx.terms.get(args[0]), TermData::App(sym, some_args) if sym.name() == "logic_Some" && some_args.len() == 1)
    }

    fn is_quantifier_consumer_option_none_some_disequality(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "="
            && args.len() == 2
            && ((self.is_quantifier_consumer_logic_none(args[0])
                && self.is_quantifier_consumer_logic_some(args[1]))
                || (self.is_quantifier_consumer_logic_none(args[1])
                    && self.is_quantifier_consumer_logic_some(args[0])))
    }

    fn is_quantifier_consumer_logic_none(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => matches!(name.as_str(), "logic_None" | "None"),
            TermData::App(sym, args) => {
                matches!(sym.name(), "logic_None" | "None") && args.is_empty()
            }
            _ => false,
        }
    }

    fn is_quantifier_consumer_logic_some(&self, term: TermId) -> bool {
        matches!(
            self.ctx.terms.get(term),
            TermData::App(sym, args) if matches!(sym.name(), "logic_Some" | "Some") && args.len() == 1
        )
    }

    fn is_quantifier_consumer_seq_empty_contains_instance(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "seq_contains"
            && args.len() == 2
            && self.is_quantifier_consumer_seq_empty(args[0])
            && self.term_supported_as_uf_definition_value(args[1])
    }

    fn is_quantifier_consumer_seq_empty(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => name == "seq_empty",
            TermData::App(sym, args) => sym.name() == "seq_empty" && args.is_empty(),
            _ => false,
        }
    }

    fn is_quantifier_consumer_seq_len_nonnegative_instance(&self, args: &[TermId]) -> bool {
        args.len() == 2 && self.is_int_zero(args[0]) && self.is_quantifier_consumer_seq_len(args[1])
    }

    fn is_quantifier_consumer_seq_len_proxy_lower_bound(&self, args: &[TermId]) -> bool {
        args.len() == 2
            && self.is_int_zero(args[0])
            && self.is_quantifier_consumer_seq_len_proxy(args[1])
    }

    fn is_int_zero(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Const(Constant::Int(value)) if value == &num_bigint::BigInt::ZERO)
    }

    fn is_quantifier_consumer_seq_len_proxy(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Var(name, _) if name.starts_with("seq_len_proxy_"))
    }

    fn is_quantifier_consumer_seq_len(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "seq_len"
            && args.len() == 1
            && self.term_supported_as_uf_definition_value(args[0])
    }

    fn is_quantifier_consumer_bucket_guarded_frame_clause(&self, args: &[TermId]) -> bool {
        if args.len() < 2 {
            return false;
        }
        let mut saw_bucket_guard = false;
        for &arg in args {
            if self.is_negated_quantifier_consumer_bucket_ix_comparison(arg) {
                saw_bucket_guard = true;
            } else if !self.term_supported_as_uf_definition_condition(arg) {
                return false;
            }
        }
        saw_bucket_guard
    }

    fn is_negated_quantifier_consumer_bucket_ix_comparison(&self, term: TermId) -> bool {
        let TermData::Not(inner) = self.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
            return false;
        };
        matches!(sym.name(), "<" | "<=" | ">" | ">=")
            && args.len() == 2
            && (self.is_quantifier_consumer_bucket_ix(args[0])
                || self.is_quantifier_consumer_bucket_ix(args[1]))
    }

    fn is_quantifier_consumer_bucket_ix(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "logic_bucket__ix"
            && args.len() == 2
            && args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_value(arg))
    }

    fn quantifier_consumer_or_has_simple_satisfiable_branch(&self, args: &[TermId]) -> bool {
        args.iter().copied().any(|arg| {
            self.quantifier_consumer_simple_branch_supported(arg)
                && self.quantifier_consumer_branch_consistent(arg)
        })
    }

    fn quantifier_consumer_simple_branch_supported(&self, term: TermId) -> bool {
        if self.term_contains_int_div_mod(term) {
            return false;
        }
        let (predicate, inner) = match self.ctx.terms.get(term) {
            TermData::Not(inner) => (true, *inner),
            _ => (false, term),
        };
        let TermData::App(sym, args) = self.ctx.terms.get(inner) else {
            return false;
        };
        if matches!(sym.name(), "=" | "distinct" | "<" | "<=" | ">" | ">=")
            && args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_value(arg))
            && (!predicate || sym.name() == "=")
        {
            return true;
        }
        args.iter()
            .copied()
            .all(|arg| self.term_supported_as_uf_definition_value(arg))
            && (is_quantifier_consumer_completable_bool_predicate(sym.name())
                || self.is_quantifier_consumer_datatype_tester(sym.name()))
    }

    fn quantifier_consumer_branch_consistent(&self, branch: TermId) -> bool {
        if self.quantifier_consumer_branch_has_direct_boolean_conflict(branch) {
            return false;
        }
        let mut assertions = self.ctx.assertions.clone();
        assertions.push(branch);
        !self.assertions_have_simple_int_contradiction(&assertions)
    }

    fn quantifier_consumer_branch_has_direct_boolean_conflict(&self, branch: TermId) -> bool {
        match self.ctx.terms.get(branch) {
            TermData::Not(inner) => self.ctx.assertions.contains(inner),
            _ => self.ctx.assertions.iter().any(|&assertion| {
                matches!(self.ctx.terms.get(assertion), TermData::Not(inner) if *inner == branch)
            }),
        }
    }

    fn is_quantifier_consumer_datatype_tester(&self, name: &str) -> bool {
        let Some(ctor_name) = name.strip_prefix("is-") else {
            return false;
        };
        self.ctx.is_constructor(ctor_name).is_some() || !ctor_name.is_empty()
    }

    fn is_true_datatype_tester_instance(&self, name: &str, args: &[TermId]) -> bool {
        if args.len() != 1 {
            return false;
        }
        let Some(ctor_name) = name.strip_prefix("is-") else {
            return false;
        };
        if self.ctx.is_constructor(ctor_name).is_none() {
            return false;
        }
        match self.ctx.terms.get(args[0]) {
            TermData::App(sym, _) => sym.name() == ctor_name,
            TermData::Var(name, _) => name == ctor_name,
            _ => false,
        }
    }

    fn is_single_constructor_datatype_tester_instance(&self, name: &str, args: &[TermId]) -> bool {
        if args.len() != 1 || !self.term_supported_as_uf_definition_value(args[0]) {
            return false;
        }
        let Some(ctor_name) = name.strip_prefix("is-") else {
            return false;
        };
        let Some((dt_name, _)) = self.ctx.is_constructor(ctor_name) else {
            return false;
        };
        self.ctx.datatype_iter().any(|(dt, ctors)| {
            dt == dt_name.as_str()
                && ctors.len() == 1
                && ctors.first().is_some_and(|ctor| ctor == ctor_name)
        })
    }

    fn term_contains_int_div_mod(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        let mut seen = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if matches!(sym.name(), "div" | "mod") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    stack.push(*cond);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        false
    }

    fn is_quantifier_consumer_seq_get_in_bounds_instance(&self, args: &[TermId]) -> bool {
        if args.len() != 3 {
            return false;
        }
        for eq_idx in 0..3 {
            let Some((seq, index)) = self.quantifier_consumer_seq_get_value_eq(args[eq_idx]) else {
                continue;
            };
            let mut saw_lower = false;
            let mut saw_upper = false;
            for (idx, &arg) in args.iter().enumerate() {
                if idx == eq_idx {
                    continue;
                }
                if self.is_negated_le_zero(arg, index) {
                    saw_lower = true;
                } else if self.is_negated_lt_index_seq_len(arg, index, seq) {
                    saw_upper = true;
                }
            }
            if saw_lower && saw_upper {
                return true;
            }
        }
        false
    }

    fn quantifier_consumer_seq_get_value_eq(&self, term: TermId) -> Option<(TermId, TermId)> {
        let [lhs, rhs] = self.eq_args(term)?;
        self.quantifier_consumer_seq_get_value_side(lhs, rhs)
            .or_else(|| self.quantifier_consumer_seq_get_value_side(rhs, lhs))
    }

    fn quantifier_consumer_seq_get_value_side(
        &self,
        get_term: TermId,
        value_term: TermId,
    ) -> Option<(TermId, TermId)> {
        let TermData::App(get_sym, get_args) = self.ctx.terms.get(get_term) else {
            return None;
        };
        if get_sym.name() != "seq_get" || get_args.len() != 2 {
            return None;
        }
        let TermData::App(some_sym, some_args) = self.ctx.terms.get(value_term) else {
            return None;
        };
        if some_sym.name() != "logic_Some" || some_args.len() != 1 {
            return None;
        }
        let TermData::App(index_sym, index_args) = self.ctx.terms.get(some_args[0]) else {
            return None;
        };
        if index_sym.name() == "seq_index_logic"
            && index_args.len() == 2
            && index_args[0] == get_args[0]
            && index_args[1] == get_args[1]
        {
            Some((get_args[0], get_args[1]))
        } else {
            None
        }
    }

    fn is_negated_le_zero(&self, term: TermId, index: TermId) -> bool {
        let TermData::Not(inner) = self.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
            return false;
        };
        sym.name() == "<=" && args.len() == 2 && self.is_int_zero(args[0]) && args[1] == index
    }

    fn is_negated_lt_index_seq_len(&self, term: TermId, index: TermId, seq: TermId) -> bool {
        let TermData::Not(inner) = self.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = self.ctx.terms.get(*inner) else {
            return false;
        };
        sym.name() == "<"
            && args.len() == 2
            && args[0] == index
            && self.is_quantifier_consumer_seq_len_of(args[1], seq)
    }

    fn is_quantifier_consumer_seq_len_of(&self, term: TermId, seq: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "seq_len" && args.len() == 1 && args[0] == seq
    }

    fn quantifier_consumer_view_variable_alias_equality(&self, lhs: TermId, rhs: TermId) -> bool {
        if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return false;
        }
        let TermData::Var(lhs_name, _) = self.ctx.terms.get(lhs) else {
            return false;
        };
        let TermData::Var(rhs_name, _) = self.ctx.terms.get(rhs) else {
            return false;
        };
        lhs_name
            .strip_suffix("_view")
            .is_some_and(|base| base == rhs_name)
            || rhs_name
                .strip_suffix("_view")
                .is_some_and(|base| base == lhs_name)
    }

    fn quantifier_consumer_seq_index_restore_bridge_equality(
        &self,
        select_side: TermId,
        elem_side: TermId,
    ) -> bool {
        let TermData::App(select_sym, select_args) = self.ctx.terms.get(select_side) else {
            return false;
        };
        if select_sym.name() != "select" || select_args.len() != 2 {
            return false;
        }
        if !self.is_quantifier_consumer_seq_array(select_args[0]) {
            return false;
        }
        let Some((seq, offset_index)) =
            self.quantifier_consumer_seq_offset_plus_index(select_args[1])
        else {
            return false;
        };
        let TermData::App(elem_sym, elem_args) = self.ctx.terms.get(elem_side) else {
            return false;
        };
        if elem_sym.name() != "__seq_elem_List" || elem_args.len() != 1 {
            return false;
        }
        let TermData::App(restore_sym, restore_args) = self.ctx.terms.get(elem_args[0]) else {
            return false;
        };
        restore_sym.name() == "__seq_index_restore_List"
            && restore_args.len() == 2
            && restore_args[0] == seq
            && restore_args[1] == offset_index
    }

    fn is_quantifier_consumer_seq_array(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "seq_array" && args.len() == 1
    }

    fn quantifier_consumer_seq_offset_plus_index(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "+" || args.len() != 2 {
            return None;
        }
        let seq = self.quantifier_consumer_seq_offset_arg(args[0])?;
        Some((seq, args[1]))
    }

    fn quantifier_consumer_seq_offset_arg(&self, term: TermId) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        (sym.name() == "seq_offset" && args.len() == 1).then(|| args[0])
    }

    fn quantifier_consumer_seq_elem_injectivity_forced_false(&self, term: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "or" {
            return false;
        }
        let Some((x, y, elem_x, elem_y)) =
            self.quantifier_consumer_seq_elem_injectivity_parts(args)
        else {
            return false;
        };
        self.assertions_force_not_equal(x, y) && self.assertions_force_equal(elem_x, elem_y)
    }

    fn is_quantifier_consumer_seq_elem_injectivity_instance(&self, args: &[TermId]) -> bool {
        self.quantifier_consumer_seq_elem_injectivity_parts(args)
            .is_some()
    }

    fn quantifier_consumer_seq_elem_injectivity_parts(
        &self,
        args: &[TermId],
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        if args.len() != 2 {
            return None;
        }
        self.quantifier_consumer_seq_elem_injectivity_parts_ordered(args[0], args[1])
            .or_else(|| {
                self.quantifier_consumer_seq_elem_injectivity_parts_ordered(args[1], args[0])
            })
    }

    fn quantifier_consumer_seq_elem_injectivity_parts_ordered(
        &self,
        eq_term: TermId,
        diseq_term: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let [x, y] = self.eq_args(eq_term)?;
        let TermData::Not(inner) = self.ctx.terms.get(diseq_term) else {
            return None;
        };
        let [elem_lhs, elem_rhs] = self.eq_args(*inner)?;
        let elem_lhs_arg = self.quantifier_consumer_seq_elem_arg(elem_lhs)?;
        let elem_rhs_arg = self.quantifier_consumer_seq_elem_arg(elem_rhs)?;
        if (elem_lhs_arg == x && elem_rhs_arg == y) || (elem_lhs_arg == y && elem_rhs_arg == x) {
            Some((x, y, elem_lhs, elem_rhs))
        } else {
            None
        }
    }

    fn eq_args(&self, term: TermId) -> Option<[TermId; 2]> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() == "=" && args.len() == 2 {
            Some([args[0], args[1]])
        } else {
            None
        }
    }

    fn quantifier_consumer_seq_elem_arg(&self, term: TermId) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() == "__seq_elem_List" && args.len() == 1 {
            Some(args[0])
        } else {
            None
        }
    }

    fn assertions_force_equal(&self, lhs: TermId, rhs: TermId) -> bool {
        self.ctx.assertions.iter().copied().any(|assertion| {
            self.eq_args(assertion)
                .is_some_and(|[a, b]| same_pair(a, b, lhs, rhs))
        })
    }

    fn assertions_force_not_equal(&self, lhs: TermId, rhs: TermId) -> bool {
        self.ctx.assertions.iter().copied().any(|assertion| {
            let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
                return false;
            };
            self.eq_args(*inner)
                .is_some_and(|[a, b]| same_pair(a, b, lhs, rhs))
        })
    }

    fn equality_supported_by_uf_completion(&self, lhs: TermId, rhs: TermId) -> bool {
        if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return false;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(lhs) else {
            return false;
        };
        if args.len() != 1 || !is_mbqi_completable_uf_symbol(sym.name()) {
            return false;
        }
        if args[0] == rhs {
            return true;
        }
        let TermData::App(inner_sym, inner_args) = self.ctx.terms.get(args[0]) else {
            return false;
        };
        inner_args.len() == 1
            && inner_args[0] == rhs
            && is_mbqi_completable_uf_symbol(inner_sym.name())
    }

    /// The defined head `f(x⃗)` of a UF-DEFINITION `forall`, i.e. a body of the
    /// shape `(= (f x⃗) rhs(x⃗))` (either orientation) where
    ///
    ///   * `f` is a free uninterpreted symbol (not a theory operator, not a
    ///     datatype selector/constructor),
    ///   * its arguments are EXACTLY the quantifier's binders, each used once —
    ///     so every ground instantiation pins `f` at one independent point, and
    ///   * `f` does not reappear on the value side — so the axiom is a pointwise
    ///     assignment, not a fixpoint constraint coupling `f`'s value at one
    ///     point to its value at another (the Seq-`reverse` shape).
    ///
    /// For such a `forall`, `f`'s value at a point NOT mentioned by any ground
    /// assertion is unconstrained: the model is free to define it as `rhs` there.
    /// This is the shape predicate behind the MBQI phantom-counterexample guard
    /// in `try_mbqi_refinement`.
    ///
    /// Deliberately PURELY SYNTACTIC and *not* routed through
    /// `uf_definition_supported_by_completion`: that predicate is a
    /// *certification* (it licenses claiming an instance TRUE, so it must
    /// exclude e.g. div/mod value sides — #8969 popcount wrong-SAT). This one
    /// only licenses DECLINING TO INSTANTIATE at an unconstrained point, which
    /// withholds a valid consequence and can therefore only cost completeness
    /// (`Unknown`), never soundness. Both are needed and neither implies the
    /// other.
    /// MBQI SAT-certification gate (#special-relations-mbqi-sat).
    ///
    /// Decide whether the ground instance `ground_body` (a leaf `forall` body
    /// with its binders replaced by ground terms) may be soundly added as an
    /// MBQI lemma that PINS an otherwise-undefined uninterpreted predicate at a
    /// finite ground point — the missing step that lets a lone special-relations
    /// order constraint reach a genuine SAT verdict instead of
    /// `Unknown(QuantifierUnhandled)`.
    ///
    /// Admissible only when adding the instance introduces NO new domain element
    /// of the (finite) uninterpreted binder universe:
    /// * every bound variable ranges over a freely-finite UNINTERPRETED sort (a
    ///   declared sort, not a datatype and not an interpreted theory sort) — this
    ///   confines the rule to special-relations-shaped universals and keeps it
    ///   clear of arithmetic/BV/array quantifiers whose bodies can synthesize
    ///   unboundedly many fresh ground terms; and
    /// * every subterm of `ground_body` whose sort is one of those binder sorts
    ///   is ALREADY a known ground term of that sort.
    ///
    /// TERMINATION: with no new binder-sort element the candidate universe cannot
    /// grow, so the instantiation fixpoint is reached in finitely many rounds
    /// (order axioms build only Bool-sorted atoms over the fixed constant set).
    ///
    /// SOUNDNESS: the added instance is the asserted universal specialized to
    /// ground terms — a logical CONSEQUENCE — so it can never manufacture a wrong
    /// UNSAT, and it is only ADDED, never used to claim the point verified: the
    /// caller still clears `all_satisfied` this round, so a SAT verdict is only
    /// reached in a LATER round once the re-solved model pins the point to a
    /// concrete Bool that the quick-check re-confirms.
    fn mbqi_ground_instance_pins_finite_universe(
        &self,
        vars: &[(String, Sort)],
        ground_body: TermId,
        ground_by_sort: &HashMap<Sort, Vec<TermId>>,
    ) -> bool {
        let mut binder_sorts: HashSet<Sort> = HashSet::default();
        for (_name, sort) in vars {
            if !matches!(sort, Sort::Uninterpreted(_)) || self.binder_sort_is_datatype(sort) {
                return false;
            }
            binder_sorts.insert(sort.clone());
        }

        // No new domain element: every subterm of the ground instance whose sort
        // is a binder sort must already be a known ground term of that sort.
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![ground_body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let sort = self.ctx.terms.sort(t);
            if binder_sorts.contains(sort)
                && !ground_by_sort.get(sort).is_some_and(|ts| ts.contains(&t))
            {
                return false;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_t, else_t) => {
                    stack.push(*cond);
                    stack.push(*then_t);
                    stack.push(*else_t);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        }
        true
    }

    fn forall_uf_definition_head(&self, vars: &[(String, Sort)], body: TermId) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(body) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (args[0], args[1]);
        self.uf_definition_head_side(vars, lhs, rhs)
            .or_else(|| self.uf_definition_head_side(vars, rhs, lhs))
    }

    /// One orientation of [`Self::forall_uf_definition_head`]: is `head` an
    /// application of a free UF to exactly the distinct binders, with the
    /// symbol absent from `value`?
    fn uf_definition_head_side(
        &self,
        vars: &[(String, Sort)],
        head: TermId,
        value: TermId,
    ) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(head) else {
            return None;
        };
        let name = sym.name();
        if args.is_empty()
            || args.len() != vars.len()
            || !is_mbqi_completable_uf_symbol(name)
            || self.symbol_is_datatype_selector_or_constructor(name)
        {
            return None;
        }
        // Arguments must be exactly the binders, each used once (any order).
        let mut used: Vec<bool> = vec![false; vars.len()];
        for &arg in args {
            let TermData::Var(arg_name, _) = self.ctx.terms.get(arg) else {
                return None;
            };
            let idx = vars.iter().position(|(n, _)| n == arg_name)?;
            if std::mem::replace(&mut used[idx], true) {
                return None;
            }
        }
        // Pointwise, not a fixpoint constraint on `f` itself.
        if self.term_applies_symbol(value, name) {
            return None;
        }
        Some(head)
    }

    fn same_sort_variable_equality(&self, lhs: TermId, rhs: TermId) -> bool {
        let lhs_sort = self.ctx.terms.sort(lhs);
        if lhs_sort != self.ctx.terms.sort(rhs) {
            return false;
        }
        // SOUNDNESS (#enum-forall / #3 BV-forall wrong-sat): a bare `(= u v)`
        // between two same-sort variables is completion-safe ONLY for a *freely
        // collapsible* sort — one whose interpretation the UF-completion model is
        // free to shrink to a single element so that `u` and `v` may be
        // identified. That is exactly an *uninterpreted* sort that is not a
        // datatype. Every other sort has a fixed, ground-determined domain with
        // at least two distinct elements (or infinitely many), so `(forall (u v)
        // (= u v))` is genuinely UNSAT and must NOT be accepted as a satisfiable
        // completion:
        //   - BitVec(w): 2^w distinct values (q0=0, q1=1 falsifies) — the #3 bug.
        //   - Bool: true != false. Int/Real: infinitely many distinct values.
        //   - String/RegLan/FloatingPoint/Array/Seq: >= 2 distinct elements.
        // A datatype sort surfaces as `Sort::Uninterpreted(name)` but its nullary
        // constructors are distinct `Var`s, so `(forall (c E) (= c R))` is also
        // UNSAT; `binder_sort_is_datatype` excludes those. Restricting acceptance
        // to non-datatype uninterpreted sorts fails all interpreted-sort cases
        // closed (the soundness gate degrades the ground `sat` to `unknown` via
        // MBQI). Genuine UF definitions over interpreted-sorted receivers
        // (`forall self k. f(self,k) = ...`) are unaffected: they route through
        // `uf_definition_supported_by_completion`, not this var-var path.
        if !matches!(lhs_sort, Sort::Uninterpreted(_)) || self.binder_sort_is_datatype(lhs_sort) {
            return false;
        }
        matches!(self.ctx.terms.get(lhs), TermData::Var(_, _))
            && matches!(self.ctx.terms.get(rhs), TermData::Var(_, _))
    }

    fn quantifier_is_constant_uf_definition(&self, vars: &[(String, Sort)], body: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(body) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        self.constant_uf_definition_side(vars, args[0], args[1])
            || self.constant_uf_definition_side(vars, args[1], args[0])
    }

    fn quantifier_is_uf_definition(&self, _vars: &[(String, Sort)], body: TermId) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(body) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        // Deliberately does not thread the quantifier's bound variables into
        // the atom-freedom gate. This is only a syntactic family hint used to
        // schedule sound UNSAT refutation probes; it grants no SAT authority.
        // Keeping the accepted set narrow avoids wasting those probes on the
        // popcount div/mod shape (#8969).
        self.uf_definition_supported_by_completion(args[0], args[1])
            || self.uf_definition_supported_by_completion(args[1], args[0])
    }

    /// True when `term` contains an application of `symbol` anywhere
    /// (including under binders and lets).
    fn term_applies_symbol(&self, term: TermId, symbol: &str) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == symbol {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    fn uf_definition_supported_by_completion(&self, uf_side: TermId, value_side: TermId) -> bool {
        if self.ctx.terms.sort(uf_side) != self.ctx.terms.sort(value_side) {
            return false;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(uf_side) else {
            return false;
        };
        // SOUNDNESS (#enum-forall struct case): a datatype *selector* or
        // *constructor* is not a free uninterpreted function — its value is
        // pinned by the datatype's constructor semantics. So `(forall (p P)
        // (= (f p) 0))` over `P ((mk (f Int)))` is a structural constraint
        // (refuted by any `p` with `(f p) != 0`), NOT a benign UF definition;
        // treating it as completion-safe yields a wrong `sat` (correct: UNSAT).
        // Fail closed. Genuine QuantifierConsumer definitions over datatype *receivers* use
        // declared free UFs (`logic_bucket__ix`, `logic_field_buckets`), not
        // auto-generated selectors, so they are unaffected.
        if self.symbol_is_datatype_selector_or_constructor(sym.name()) {
            return false;
        }
        if self.term_contains_int_div_mod(value_side)
            && !is_quantifier_consumer_completion_arith_uf_symbol(sym.name())
        {
            return false;
        }
        // SOUNDNESS (#seq-axiom wrong-SAT, 2026-07-05): the defined symbol
        // must not reappear on the value side. `reverse(push_back(s, x)) =
        // push_front(reverse(s), x)` (verification-consumer's Seq reverse axiom R4) is a
        // FIXPOINT constraint coupling `f`'s value at one point to its value
        // at another — not a pointwise assignment — so there is no completion
        // freedom (same rule as
        // `quantifier_is_pointwise_materializable_uf_definition`). Certifying
        // it as a benign "UF definition" let the UF-completion certificate
        // promote a ground Unknown/Sat to SAT on a genuinely UNSAT query
        // (z3: unsat). Applies to quantifier bodies AND ground instances —
        // an instantiated fixpoint constraint is just as coupled.
        //
        // EXEMPTION (#concat-len, 2026-07-10): the quantifier_consumer length homomorphism
        // `seq_len(seq_concat l r) = seq_len(l) + seq_len(r)` is the one
        // recognized self-referential shape with a known TOTAL completion —
        // the standard list model interprets every quantifier_consumer Seq symbol and
        // satisfies it, and the recursion structurally descends (len at the
        // concat is defined from lens of its two strict subterms), so any
        // partial assignment on generators extends. R4-style same-size
        // couplings stay rejected. Blanket rejection here regressed the two
        // seq_concat_len verification-consumer reducers to instant Unknown.
        if self.term_applies_symbol(value_side, sym.name())
            && !self.is_quantifier_consumer_concat_len_definition(uf_side, value_side)
        {
            return false;
        }
        !args.is_empty()
            && is_mbqi_completable_uf_symbol(sym.name())
            && args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, false))
            && self.term_supported_as_uf_definition_value_ext(value_side, false)
    }

    /// The quantifier_consumer Seq length homomorphism `seq_len(seq_concat l r) =
    /// (+ (seq_len l) (seq_len r))` (either summand order), checked
    /// structurally on the already-split equality sides. See the #concat-len
    /// exemption in [`Self::uf_definition_supported_by_completion`].
    fn is_quantifier_consumer_concat_len_definition(
        &self,
        uf_side: TermId,
        value_side: TermId,
    ) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(uf_side) else {
            return false;
        };
        if sym.name() != "seq_len" || args.len() != 1 {
            return false;
        }
        let TermData::App(inner, cat_args) = self.ctx.terms.get(args[0]) else {
            return false;
        };
        if inner.name() != "seq_concat" || cat_args.len() != 2 {
            return false;
        }
        let (l, r) = (cat_args[0], cat_args[1]);
        let TermData::App(plus, sum_args) = self.ctx.terms.get(value_side) else {
            return false;
        };
        if plus.name() != "+" || sum_args.len() != 2 {
            return false;
        }
        let len_arg = |t: TermId| match self.ctx.terms.get(t) {
            TermData::App(s, a) if s.name() == "seq_len" && a.len() == 1 => Some(a[0]),
            _ => None,
        };
        match (len_arg(sum_args[0]), len_arg(sum_args[1])) {
            (Some(a), Some(b)) => (a == l && b == r) || (a == r && b == l),
            _ => false,
        }
    }

    /// True when `name` is a datatype selector or constructor. Such symbols are
    /// interpreted by constructor semantics (not free), so an equality with one
    /// as its head is a structural constraint, not a UF-completion definition.
    pub(in crate::executor) fn symbol_is_datatype_selector_or_constructor(
        &self,
        name: &str,
    ) -> bool {
        self.ctx
            .ctor_selectors_iter()
            .any(|(ctor, sels)| ctor == name || sels.iter().any(|s| s == name))
    }

    fn constant_uf_definition_side(
        &self,
        vars: &[(String, Sort)],
        uf_side: TermId,
        value_side: TermId,
    ) -> bool {
        if self.ctx.terms.sort(uf_side) != self.ctx.terms.sort(value_side) {
            return false;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(uf_side) else {
            return false;
        };
        if args.is_empty() || !is_mbqi_completable_uf_symbol(sym.name()) {
            return false;
        }
        // SOUNDNESS (#enum-forall struct case): see
        // `uf_definition_supported_by_completion` — a selector/constructor head
        // is a structural constraint, not a free-UF definition.
        if self.symbol_is_datatype_selector_or_constructor(sym.name()) {
            return false;
        }
        let bound_names: HashSet<String> = vars.iter().map(|(name, _)| name.clone()).collect();
        !self.term_contains_bound_var(value_side, &bound_names)
            && self.term_supported_as_constant_uf_value(value_side)
    }

    fn term_contains_bound_var(&self, term: TermId, bound_names: &HashSet<String>) -> bool {
        fn visit(
            terms: &ay_core::TermStore,
            term: TermId,
            bound_names: &HashSet<String>,
            seen: &mut HashSet<TermId>,
        ) -> bool {
            if !seen.insert(term) {
                return false;
            }
            match terms.get(term) {
                TermData::Var(name, _) => bound_names.contains(name),
                TermData::App(_, args) => args
                    .iter()
                    .copied()
                    .any(|arg| visit(terms, arg, bound_names, seen)),
                TermData::Not(inner) => visit(terms, *inner, bound_names, seen),
                TermData::Ite(cond, then_term, else_term) => {
                    visit(terms, *cond, bound_names, seen)
                        || visit(terms, *then_term, bound_names, seen)
                        || visit(terms, *else_term, bound_names, seen)
                }
                TermData::Let(bindings, body) => {
                    bindings
                        .iter()
                        .any(|(_, value)| visit(terms, *value, bound_names, seen))
                        || visit(terms, *body, bound_names, seen)
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    visit(terms, *body, bound_names, seen)
                        || triggers
                            .iter()
                            .flatten()
                            .copied()
                            .any(|trigger| visit(terms, trigger, bound_names, seen))
                }
                TermData::Const(_) => false,
                _ => false,
            }
        }

        let mut seen = HashSet::default();
        visit(&self.ctx.terms, term, bound_names, &mut seen)
    }

    fn term_supported_as_constant_uf_value(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => true,
            TermData::App(sym, args) if is_mbqi_constant_value_symbol(sym.name()) => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_constant_uf_value(arg)),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_constant_uf_condition(*cond)
                    && self.term_supported_as_constant_uf_value(*then_term)
                    && self.term_supported_as_constant_uf_value(*else_term)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .all(|(_, value)| self.term_supported_as_constant_uf_value(*value))
                    && self.term_supported_as_constant_uf_value(*body)
            }
            _ => false,
        }
    }

    fn term_supported_as_uf_definition_value(&self, term: TermId) -> bool {
        self.term_supported_as_uf_definition_value_ext(term, false)
    }

    /// `model_backed` skips the #quantifier_consumer-arith per-atom freedom gate — see
    /// `quantifier_consumer_ground_assertion_supported_by_completion_ext` for its contract.
    fn term_supported_as_uf_definition_value_ext(&self, term: TermId, model_backed: bool) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => true,
            TermData::Not(inner) => {
                self.term_supported_as_uf_definition_condition_ext(*inner, model_backed)
            }
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or" | "=>" | "xor") => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_condition_ext(arg, model_backed)),
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct" | "<" | "<=" | ">" | ">=") =>
            {
                // A pure interpreted-arithmetic comparison atom (no completable
                // UF) is a hard constraint, not a completion-arrangeable
                // condition — see `quantifier_consumer_ground_assertion_supported_by_completion`
                // (#quantifier_consumer-arith). Under `model_backed` the atom's truth is
                // established by the validated ground model, so evaluability
                // suffices.
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed))
                    && (model_backed
                        || args
                            .iter()
                            .copied()
                            .any(|arg| self.term_mentions_completable_uf(arg)))
            }
            TermData::App(sym, args)
                if is_mbqi_constant_value_symbol(sym.name())
                    || is_mbqi_completable_uf_symbol(sym.name()) =>
            {
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed))
            }
            TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed)),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_uf_definition_condition_ext(*cond, model_backed)
                    && self.term_supported_as_uf_definition_value_ext(*then_term, model_backed)
                    && self.term_supported_as_uf_definition_value_ext(*else_term, model_backed)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().all(|(_, value)| {
                    self.term_supported_as_uf_definition_value_ext(*value, model_backed)
                }) && self.term_supported_as_uf_definition_value_ext(*body, model_backed)
            }
            TermData::Forall(_, body, _) => self.term_supported_by_uf_completion(*body),
            _ => false,
        }
    }

    fn term_supported_as_uf_definition_condition(&self, term: TermId) -> bool {
        self.term_supported_as_uf_definition_condition_ext(term, false)
    }

    /// See `term_supported_as_uf_definition_value_ext` for the `model_backed`
    /// contract.
    fn term_supported_as_uf_definition_condition_ext(
        &self,
        term: TermId,
        model_backed: bool,
    ) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => true,
            TermData::Not(inner) => {
                self.term_supported_as_uf_definition_condition_ext(*inner, model_backed)
            }
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or" | "=>" | "xor") => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_condition_ext(arg, model_backed)),
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct" | "<" | "<=" | ">" | ">=") =>
            {
                // See `quantifier_consumer_ground_assertion_supported_by_completion`: a pure
                // interpreted-arithmetic atom has no completion freedom and must
                // not be claimed supported (#quantifier_consumer-arith) unless `model_backed`
                // (see `term_supported_as_uf_definition_value_ext`).
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed))
                    && (model_backed
                        || args
                            .iter()
                            .copied()
                            .any(|arg| self.term_mentions_completable_uf(arg)))
            }
            TermData::App(sym, args) if is_mbqi_completable_uf_symbol(sym.name()) => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_uf_definition_value_ext(arg, model_backed)),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_uf_definition_condition_ext(*cond, model_backed)
                    && self.term_supported_as_uf_definition_condition_ext(*then_term, model_backed)
                    && self.term_supported_as_uf_definition_condition_ext(*else_term, model_backed)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().all(|(_, value)| {
                    self.term_supported_as_uf_definition_condition_ext(*value, model_backed)
                }) && self.term_supported_as_uf_definition_condition_ext(*body, model_backed)
            }
            TermData::Forall(_, body, _) => self.term_supported_by_uf_completion(*body),
            _ => false,
        }
    }

    fn term_supported_as_constant_uf_condition(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => true,
            TermData::Not(inner) => self.term_supported_as_constant_uf_condition(*inner),
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct" | "<" | "<=" | ">" | ">=") =>
            {
                args.iter()
                    .copied()
                    .all(|arg| self.term_supported_as_constant_uf_value(arg))
            }
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or" | "=>" | "xor") => args
                .iter()
                .copied()
                .all(|arg| self.term_supported_as_constant_uf_condition(arg)),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_supported_as_constant_uf_condition(*cond)
                    && self.term_supported_as_constant_uf_condition(*then_term)
                    && self.term_supported_as_constant_uf_condition(*else_term)
            }
            _ => false,
        }
    }

    /// Synthesize default candidate terms for sorts with no existing ground terms.
    ///
    /// For each sort in `needed_sorts`, creates a small set of candidate TermIds
    /// by combining theory defaults with values from the current model.
    ///
    /// Strategy per sort (mirrors Z3 `replace_model_value` + `get_some_value`):
    /// - `Bool`: `true`, `false`
    /// - `Int`: `0` + all distinct Int values from the LIA/EUF model
    /// - `Real`: `0.0` + all distinct Real values from the LRA model
    /// - `BitVec(w)`: `0` of width `w` + model values from the BV model
    /// - `String`: `""` (empty string)
    /// - `Uninterpreted(name)`: fresh constant per element in the EUF sort universe
    /// - Other sorts: no candidates (MBQI skips these quantifiers)
    fn synthesize_mbqi_candidates(
        &mut self,
        needed_sorts: &HashSet<Sort>,
    ) -> HashMap<Sort, Vec<TermId>> {
        let mut result: HashMap<Sort, Vec<TermId>> = HashMap::default();

        for sort in needed_sorts {
            let mut candidates: Vec<TermId> = Vec::new();

            match sort {
                Sort::Bool => {
                    candidates.push(self.ctx.terms.mk_bool(true));
                    candidates.push(self.ctx.terms.mk_bool(false));
                }
                Sort::Int => {
                    // Default: 0
                    candidates.push(self.ctx.terms.mk_int(num_bigint::BigInt::ZERO));
                    // Add distinct model values from LIA/EUF.
                    if let Some(ref model) = self.last_model {
                        let mut seen_values: HashSet<num_bigint::BigInt> = HashSet::default();
                        seen_values.insert(num_bigint::BigInt::ZERO);
                        if let Some(ref lia_model) = model.lia_model {
                            for val in lia_model.values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                if seen_values.insert(val.clone()) {
                                    candidates.push(self.ctx.terms.mk_int(val.clone()));
                                }
                            }
                        }
                        if let Some(ref euf_model) = model.euf_model {
                            for val in euf_model.int_values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                if seen_values.insert(val.clone()) {
                                    candidates.push(self.ctx.terms.mk_int(val.clone()));
                                }
                            }
                        }
                    }
                }
                Sort::Real => {
                    // Default: 0.0
                    candidates.push(self.ctx.terms.mk_rational(num_rational::BigRational::new(
                        num_bigint::BigInt::ZERO,
                        num_bigint::BigInt::from(1),
                    )));
                    // Add model values from LRA.
                    if let Some(ref model) = self.last_model {
                        let mut seen: HashSet<TermId> = candidates.iter().copied().collect();
                        if let Some(ref lra_model) = model.lra_model {
                            for val in lra_model.values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                let term = self.ctx.terms.mk_rational(val.clone());
                                if seen.insert(term) {
                                    candidates.push(term);
                                }
                            }
                        }
                    }
                }
                Sort::BitVec(bv_sort) => {
                    let width = bv_sort.width;
                    // Default: 0 of this width
                    candidates.push(self.ctx.terms.mk_bitvec(num_bigint::BigInt::ZERO, width));
                    // Add model values from BV.
                    if let Some(ref model) = self.last_model {
                        let mut seen: HashSet<TermId> = candidates.iter().copied().collect();
                        if let Some(ref bv_model) = model.bv_model {
                            for (&term_id, _) in &bv_model.values {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                // Only use values whose term has matching BV width
                                if self.ctx.terms.sort(term_id) == &Sort::BitVec(bv_sort.clone())
                                    && seen.insert(term_id)
                                {
                                    candidates.push(term_id);
                                }
                            }
                        }
                    }
                }
                Sort::String => {
                    // Empty plus short non-empty witnesses. A `forall` over
                    // String whose body is falsified only by a NON-empty string
                    // (e.g. `forall s. str.len(s) = 0` with `str.len("hello")=5`
                    // asserted) would otherwise never be refuted — MBQI only
                    // tried "" — yielding a wrong SAT (#quant-string). Adding
                    // witnesses is sound: it can only turn a wrong SAT into UNSAT
                    // (a genuine SAT holds for every string, including these),
                    // never the reverse.
                    candidates.push(self.ctx.terms.mk_string(String::new()));
                    candidates.push(self.ctx.terms.mk_string("A".to_string()));
                    candidates.push(self.ctx.terms.mk_string("AB".to_string()));
                }
                Sort::Uninterpreted(name) => {
                    // Use the EUF model's sort universe to get concrete elements.
                    // Each element (e.g., "@Color!0") becomes a fresh constant.
                    if let Some(ref model) = self.last_model {
                        if let Some(ref euf_model) = model.euf_model {
                            if let Some(elements) = euf_model.sort_elements.get(name) {
                                for elem_name in elements {
                                    if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                        break;
                                    }
                                    let sort_clone = sort.clone();
                                    let term = self.ctx.terms.mk_var(elem_name.clone(), sort_clone);
                                    candidates.push(term);
                                }
                            }
                        }
                    }
                    // If no universe elements, create a single fresh constant.
                    if candidates.is_empty() {
                        let fresh_name = self.ctx.terms.mk_internal_symbol("mbqi_elem");
                        let term = self.ctx.terms.mk_var(fresh_name, sort.clone());
                        candidates.push(term);
                    }
                }
                Sort::Array(arr_sort) => {
                    // Synthesize (as const (Array I E) d) where `d` is a default
                    // value for the element sort E. This gives MBQI a concrete
                    // array instance to substitute for array-sorted bound
                    // variables, which is how quantifiers over arrays can be
                    // refuted against the current model.
                    //
                    // Soundness note: const-array is a legitimate array value,
                    // so evaluating the quantifier body against it is a valid
                    // quick-check instantiation. If the body evaluates to
                    // false, we get a real counterexample. If true, MBQI
                    // continues with other candidates (none, here) and
                    // reports incomplete — which is strictly better than
                    // accepting the unverified SAT. See #8729 (Z3#6303
                    // byte-concat quantifier reproducer).
                    if let Some(default) = self.default_term_for_sort(&arr_sort.element_sort) {
                        let const_arr = self
                            .ctx
                            .terms
                            .mk_const_array(arr_sort.index_sort.clone(), default);
                        candidates.push(const_arr);
                    }
                }
                // FP, Seq, Datatype, RegLan: complex sorts where synthesizing
                // defaults is non-trivial. MBQI skips these for now — future
                // work could handle them via model-based construction.
                _ => {}
            }

            if !candidates.is_empty() {
                result.insert(sort.clone(), candidates);
            }
        }

        result
    }

    /// Build a canonical default term of the given sort for MBQI synthesis.
    ///
    /// Returns `None` for sorts where no sound default exists in this
    /// context (FP, Seq, Datatype, RegLan) — the caller should then skip
    /// generating candidates for containers that depend on this sort.
    ///
    /// This is a helper for array candidate synthesis (#8729): we need a
    /// concrete element value to build `(as const (Array I E) d)` when a
    /// quantifier binds an array-sorted variable.
    fn default_term_for_sort(&mut self, sort: &Sort) -> Option<TermId> {
        match sort {
            Sort::Bool => Some(self.ctx.terms.mk_bool(false)),
            Sort::Int => Some(self.ctx.terms.mk_int(num_bigint::BigInt::ZERO)),
            Sort::Real => Some(self.ctx.terms.mk_rational(num_rational::BigRational::new(
                num_bigint::BigInt::ZERO,
                num_bigint::BigInt::from(1),
            ))),
            Sort::BitVec(bv_sort) => Some(
                self.ctx
                    .terms
                    .mk_bitvec(num_bigint::BigInt::ZERO, bv_sort.width),
            ),
            Sort::String => Some(self.ctx.terms.mk_string(String::new())),
            Sort::Array(arr_sort) => {
                // Recursive case: default-init the element, then lift to
                // const-array.
                let elem = self.default_term_for_sort(&arr_sort.element_sort)?;
                Some(
                    self.ctx
                        .terms
                        .mk_const_array(arr_sort.index_sort.clone(), elem),
                )
            }
            // Uninterpreted / FP / Seq / Datatype / RegLan: no sound default
            // without consulting the model. Leave to future work.
            _ => None,
        }
    }

    /// SAT certificate for skipped LEFT-INVERSE (boxing) axioms — deductive-checks's
    /// polymorphic `Box_T`/`Unbox_T` encoding (#2774):
    ///
    /// ```text
    /// forall x:S. (= (Unbox (Box x)) x)
    /// ```
    ///
    /// possibly mixed with other skipped foralls that are UNIVERSE-INDEPENDENT
    /// shapes: unary identity definitions `forall x:T. f(x) = x`, or guarded
    /// foralls `forall x⃗. (or … G …)` with a closed disjunct `G` that the
    /// certificate's OWN evaluator proves true. deductive-checks's PRODUCTION encoder
    /// emits the Box/Unbox roundtrip as GROUND facts at concrete call sites
    /// (no live Poly quantifier), so the #2774 class also arrives as the
    /// PAIR-FREE form — `identity` alone over a boxed ground core — which
    /// this certificate accepts through the UF-graph adoption below.
    ///
    /// # Design: functionalized re-evaluation
    ///
    /// The certificate does NOT trust the prior model validation or the
    /// extracted model's function tables for the constrained heads — both are
    /// LOSSY (simplified-away applications are missing from the tables;
    /// congruence-implied values such as `Unbox` at `identity(Box y)` are
    /// missing from the per-term values; that lossiness is exactly what parked
    /// the first cut of this certificate). Instead it EXHIBITS a total model
    /// `M'` by materializing every constrained head:
    ///
    /// - `Box  := a ↦ BoxPoint(Box, a)` — a total INJECTIVE embedding of the
    ///   binder domain into the (uninterpreted) result sort's universe, one
    ///   fresh universe element per domain point ([`LiElem::BoxPoint`]);
    /// - `Unbox := BoxPoint(Box, a) ↦ a`, and the designated per-sort
    ///   fallback value everywhere off the `BoxPoint(Box, ·)` family
    ///   ([`Self::left_inverse_fallback`]) — the exact table-inverse +
    ///   arbitrary-fallback completion, total and well-defined by structural
    ///   injectivity;
    /// - each identity head `f := id`;
    ///
    /// adopting the extracted model's assignments ONLY as free CHOICES that
    /// are functional by construction — per free constant, and per
    /// unconstrained user-declared UF via a CONSTRUCTED one-entry-per-point
    /// table over the ground application graph (the UF-graph adoption
    /// fixpoint: arguments are valued under `M'` first, then the extracted
    /// value of one witnessing occurrence is installed at that `M'` point;
    /// sibling occurrences at the same point READ the table, which is
    /// exactly how a congruence-implied occurrence such as
    /// `Unbox(identity(Box y))` resolves through its `Unbox(Box y)` sibling
    /// even when the extraction lost its own value) — and then RE-EVALUATING
    /// every original ground assertion under `M'`
    /// ([`Self::left_inverse_reeval`], definite `true` required — this
    /// replaces the prior validation wholesale).
    ///
    /// GRANTS only when ALL of the following hold (fail-closed otherwise):
    /// 1. the pre-restore ground core is in the linear bv/bool/euf/lia
    ///    fragment extended with uninterpreted-sorted terms (mod/div/* still
    ///    decline, #8969) — defense-in-depth; the re-evaluator independently
    ///    enforces evaluability of everything the grant depends on;
    /// 2. at least one left-inverse axiom matches; each axiom's `Box`/`Unbox`
    ///    are distinct non-Skolem uninterpreted unary symbols with an
    ///    UNINTERPRETED `Box` result sort; and all constrained heads (`Box`s,
    ///    `Unbox`s, identity heads) are PAIRWISE DISTINCT — one materialized
    ///    interpretation per symbol, so no head is constrained twice;
    /// 3. every skipped forall is a left-inverse axiom, a unary identity
    ///    definition, or a guarded forall whose closed disjunct re-evaluates
    ///    to definite `true` UNDER THE MATERIALIZED interpretation (never
    ///    under the old model — the old evaluation could disagree with `M'`);
    /// 4. every non-`forall` original assertion is quantifier-free and
    ///    re-evaluates to definite `true` under `M'`; every top-level
    ///    original `forall` is one of `forall_quants` (nothing escapes the
    ///    shape analysis);
    /// 5. the caller-enforced coverage gate: E-matching fully instantiated
    ///    every quantifier within budget (no uninstantiated quantifier, no
    ///    instantiation-limit hit, no deferred instantiation, no existential)
    ///    — see the wiring in `try_mbqi_sat_certification`.
    ///
    /// # Why sound
    ///
    /// `M'` is a genuine first-order model: each uninterpreted sort's universe
    /// is the disjoint union of the adopted extracted elements, the per-`Box`
    /// `BoxPoint` families (closed under structural nesting — a well-founded
    /// set of finite trees even when a `Box` embeds its own result sort), and
    /// one fallback padding element; interpreted sorts keep their standard
    /// carriers. Under `M'`:
    /// - each left-inverse axiom holds at EVERY binder point:
    ///   `Unbox(Box(a)) = Unbox(BoxPoint(Box, a)) = a` by construction;
    /// - each identity definition holds at every point: `f = id`;
    /// - each accepted guarded forall holds at every point: its closed
    ///   disjunct was proven definitely true in `M'` and `or` dominates;
    /// - every ground assertion was re-evaluated to definite `true` in `M'`.
    /// Symbols the re-evaluator never interpreted (they occur only in
    /// unevaluated disjuncts of accepted guarded foralls, or nowhere) may
    /// take ANY interpretation: every definite value computed above is a
    /// function of the interpreted symbols alone, so any extension of `M'`
    /// still satisfies everything. Hence the original assertion set is
    /// satisfiable — the `Sat` is genuine. Every uncertain path (unevaluable
    /// subterm, unconstrained UF application, non-integer rational, missing
    /// model value, unknown shape, re-used head symbol, …) declines, so the
    /// certificate can only turn a fail-closed `Unknown` into a genuine
    /// `Sat`, never mask a proof and never mint a wrong SAT.
    pub(in crate::executor) fn mbqi_sat_validated_left_inverse_axioms(
        &mut self,
        original_assertions: &[TermId],
        forall_quants: &[TermId],
        mut checked_model: Model,
    ) -> Option<CheckedMbqiSatAuthority> {
        // The model is owned so the exact object checked below can be equipped
        // with its stamped ground projection, installed, and sealed. Keeping a
        // borrowed model here previously allowed the checker to validate model
        // A while `CheckedMbqiSatAuthority::for_current` sealed whatever model
        // B happened to remain in `self.last_model` after nested probes.
        let model = &checked_model;
        let debug = ay_core::misc_cli_flags().debug_cert;
        if forall_quants.is_empty() {
            return None;
        }
        // Premise 1: pre-restore ground core (the set the ground solve
        // actually decided, including E-matching instances) stays inside the
        // extended evaluable fragment. Defense-in-depth against operator
        // classes the evaluator must never meet (mod/div/*, #8969).
        let ground_evaluable = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| !contains_quantifier(&self.ctx.terms, a))
            .all(|a| self.term_in_bv_bool_euf_lia_or_uninterpreted_fragment(a));
        // Premise 3 (shape partition of the skipped foralls).
        let mut pairs: Vec<(Symbol, Symbol, Sort)> = Vec::new();
        let mut identity_heads: HashSet<Symbol> = HashSet::default();
        let mut guarded: Vec<TermId> = Vec::new();
        for &q in forall_quants {
            if let Some(pair) = self.left_inverse_axiom_symbols(q) {
                // The same axiom asserted twice pins the same interpretation
                // twice — consistent, so exact duplicates dedup.
                if !pairs.contains(&pair) {
                    pairs.push(pair);
                }
            } else if let Some(f) = self.unary_identity_definition_symbol(q) {
                identity_heads.insert(f);
            } else {
                // Deferred: guarded foralls are checked below under the
                // materialized interpretation; anything else declines there.
                guarded.push(q);
            }
        }
        if debug {
            eprintln!(
                "CERT/left-inverse: nquant={} pairs={:?} nid={} nguarded={} ground_evaluable={}",
                forall_quants.len(),
                pairs,
                identity_heads.len(),
                guarded.len(),
                ground_evaluable,
            );
        }
        // At least one MATERIALIZED head must be present: a left-inverse pair
        // or an identity definition. (deductive-checks's production encoder emits the
        // Box/Unbox roundtrip as GROUND facts at call sites — no live Poly
        // quantifier — so the #2774 class typically reaches here as
        // `identity` alone over a boxed ground core; the pinned SMT-level
        // reproducer carries the explicit axiom.) A purely-guarded mix stays
        // with the strict-fragment definitions leg.
        if !ground_evaluable || (pairs.is_empty() && identity_heads.is_empty()) {
            return None;
        }
        // Premise 2: one materialized interpretation per constrained head —
        // any symbol claimed by two roles (or by two different pairings)
        // declines.
        let mut roles: HashMap<Symbol, LiRole> = HashMap::default();
        for (box_sym, unbox_sym, binder_sort) in &pairs {
            if roles.insert(box_sym.clone(), LiRole::Box).is_some() {
                return None;
            }
            let unbox_role = LiRole::Unbox {
                box_sym: box_sym.clone(),
                result_sort: binder_sort.clone(),
            };
            if roles.insert(unbox_sym.clone(), unbox_role).is_some() {
                return None;
            }
        }
        for f in &identity_heads {
            if roles.insert(f.clone(), LiRole::Identity).is_some() {
                return None;
            }
        }
        // Positive source authority: every non-native application head the
        // constructed model can materialize or adopt must be an exact, live,
        // ordinary free-UF declaration with one complete signature throughout
        // the authenticated root graph.  A registry spelling or a negative
        // builtin/Skolem filter is not declaration authority: definitions,
        // datatype members, theory declarations, solver internals, stale scoped
        // declarations, and raw core symbols all fail closed here.
        let checked_projection_bindings =
            self.left_inverse_checked_projection_bindings(original_assertions)?;
        let declared: HashSet<Symbol> = checked_projection_bindings
            .bindings()
            .iter()
            .map(|binding| binding.symbol().clone())
            .collect();
        if roles.keys().any(|symbol| !declared.contains(symbol)) {
            return None;
        }
        // Step 4 — UF-GRAPH ADOPTION: construct a FUNCTIONAL table for every
        // unconstrained user-declared UF over the ground application graph.
        // For each collected ground application whose argument values are
        // definite under the (partially materialized) `M'`, adopt the
        // extracted model's value for that application AT THE `M'`-VALUED
        // POINT — a free choice of interpretation, installed at most once per
        // point (functional by construction; a later application at the same
        // point reads the installed value, which is exactly how a
        // congruence-implied occurrence like `Unbox(identity(Box y))`
        // resolves through the `Box y` sibling even when its own per-term
        // value was lost). Iterated to a fixpoint because one adoption can
        // make another application's arguments definite. Applications that
        // never resolve leave no entry, and any assertion needing them
        // declines below.
        let ground_assertions: Vec<TermId> = original_assertions
            .iter()
            .copied()
            .filter(|&a| !matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();
        let mut adoption_roots: Vec<TermId> = ground_assertions.clone();
        for &q in &guarded {
            adoption_roots.extend(self.left_inverse_closed_or_disjuncts(q));
        }
        let uf_app_terms =
            self.left_inverse_collect_adoptable_apps(&adoption_roots, &roles, &declared);
        // Asserted unit equalities `(= (g t⃗) rhs)` (either orientation,
        // descending through top-level `and`) are the STRONGEST seeds: the
        // assertion itself forces the point's value, so seeding from it is
        // the only choice that can survive re-evaluation. They also cover
        // points the lossy extraction dropped entirely (e.g. the roundtrip
        // pins `Unbox_T(Box_T(v)) = v` deductive-checks emits per call site).
        let unit_equalities =
            self.left_inverse_unit_equalities(&ground_assertions, &roles, &declared);
        let mut uf_table: HashMap<LiUfKey, LiValue> = HashMap::default();
        loop {
            let mut installed = false;
            // Pass 1: unit-equality seeds — install `(g, v⃗) := eval(rhs)`
            // once both the application's arguments and the partner side are
            // definite under the current partial `M'`.
            for &(app, partner) in &unit_equalities {
                let TermData::App(sym, args) = self.ctx.terms.get(app).clone() else {
                    continue;
                };
                // Fresh memo per attempt: a `None` cached before the table
                // grew must not stick.
                let mut round_memo: HashMap<TermId, Option<LiValue>> = HashMap::default();
                let Some(arg_values) = self.left_inverse_reeval_all(
                    model,
                    &roles,
                    &declared,
                    &uf_table,
                    &mut round_memo,
                    &args,
                ) else {
                    continue;
                };
                let key: LiUfKey = (sym, arg_values);
                if uf_table.contains_key(&key) {
                    continue;
                }
                let Some(value) = self.left_inverse_reeval(
                    model,
                    &roles,
                    &declared,
                    &uf_table,
                    &mut round_memo,
                    partner,
                ) else {
                    continue;
                };
                uf_table.insert(key, value);
                installed = true;
            }
            // Pass 2: extracted-value adoption for the remaining points.
            for &app in &uf_app_terms {
                let TermData::App(sym, args) = self.ctx.terms.get(app).clone() else {
                    continue;
                };
                let mut round_memo: HashMap<TermId, Option<LiValue>> = HashMap::default();
                let Some(arg_values) = self.left_inverse_reeval_all(
                    model,
                    &roles,
                    &declared,
                    &uf_table,
                    &mut round_memo,
                    &args,
                ) else {
                    continue;
                };
                let key: LiUfKey = (sym, arg_values);
                if uf_table.contains_key(&key) {
                    // First installation wins (deterministic iteration
                    // order, unit-equality seeds before extracted values). A
                    // differing value at a sibling occurrence is NOT trusted
                    // anyway — if the difference matters, re-evaluation
                    // below fails the assertion and declines.
                    continue;
                }
                let Some(value) = self.left_inverse_adopted_app_value(model, app) else {
                    continue;
                };
                uf_table.insert(key, value);
                installed = true;
            }
            if !installed {
                break;
            }
        }
        if debug {
            eprintln!(
                "CERT/left-inverse: adopted UF table ({} points from {} apps): {uf_table:?}",
                uf_table.len(),
                uf_app_terms.len(),
            );
        }
        // Premise 4: every original assertion is accounted for — a top-level
        // forall must be one of the shape-checked `forall_quants`; everything
        // else must be quantifier-free and re-evaluate to definite true
        // under the materialized interpretation.
        let forall_set: HashSet<TermId> = forall_quants.iter().copied().collect();
        let mut memo: HashMap<TermId, Option<LiValue>> = HashMap::default();
        for &assertion in original_assertions {
            if matches!(self.ctx.terms.get(assertion), TermData::Forall(..)) {
                if !forall_set.contains(&assertion) {
                    return None;
                }
                continue;
            }
            if contains_quantifier(&self.ctx.terms, assertion) {
                // A nested quantifier (or top-level exists) is outside the
                // construction argument entirely.
                return None;
            }
            let value =
                self.left_inverse_reeval(model, &roles, &declared, &uf_table, &mut memo, assertion);
            if value != Some(LiValue::Bool(true)) {
                if debug {
                    eprintln!(
                        "CERT/left-inverse: ground assertion {assertion:?} re-evaluates to {value:?} — decline"
                    );
                }
                return None;
            }
        }
        // Premise 3 (deferred leg): each remaining forall needs a closed
        // disjunct that is definitely true under the SAME materialized
        // interpretation `M'` (or-domination then makes the forall hold at
        // every binder point of any universe).
        for &q in &guarded {
            if !self.left_inverse_guarded_forall_holds(
                model, &roles, &declared, &uf_table, &mut memo, q,
            ) {
                if debug {
                    eprintln!(
                        "CERT/left-inverse: rest quant {q:?} not universe-independent — decline"
                    );
                }
                return None;
            }
        }
        // Preserve the ground projection of the exhibited interpretation for
        // the public validation funnel. The extracted theory model is allowed
        // to omit precisely these constrained UF applications; without the
        // projection, a logically certified Sat is demoted merely because the
        // output evaluator cannot reconstruct M' from those lossy tables.
        let pins = Self::left_inverse_certificate_pins(&memo);
        checked_model.install_quantified_certificate_pins(&self.ctx.terms, pins)?;
        self.last_model = Some(checked_model);
        if debug {
            eprintln!("CERT/left-inverse: granted");
        }
        CheckedMbqiSatAuthority::for_current_with_projection_bindings(
            self,
            original_assertions,
            Some(checked_projection_bindings),
        )
    }

    fn left_inverse_certificate_pins(
        memo: &HashMap<TermId, Option<LiValue>>,
    ) -> Vec<(TermId, EvalValue)> {
        let mut values: Vec<(TermId, LiValue)> = memo
            .iter()
            .filter_map(|(&term, value)| value.clone().map(|value| (term, value)))
            .collect();
        values.sort_by_key(|(term, _)| term.0);

        let mut elements: HashMap<LiElem, String> = HashMap::default();
        values
            .into_iter()
            .map(|(term, value)| {
                let value = match value {
                    LiValue::Bool(value) => EvalValue::Bool(value),
                    LiValue::BitVec { value, width } => EvalValue::BitVec { value, width },
                    LiValue::Int(value) => EvalValue::Rational(value.into()),
                    LiValue::Elem(element) => {
                        let next = elements.len();
                        let name = elements
                            .entry(element)
                            .or_insert_with(|| format!("@ay_li!{next}"))
                            .clone();
                        EvalValue::Element(name)
                    }
                };
                (term, value)
            })
            .collect()
    }

    /// Evaluate every term of `terms` under the current partial `M'`;
    /// `Some(values)` iff ALL are definite (fail-closed otherwise).
    fn left_inverse_reeval_all(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        terms: &[TermId],
    ) -> Option<Vec<LiValue>> {
        let mut values = Vec::with_capacity(terms.len());
        for &term in terms {
            values.push(self.left_inverse_reeval(model, roles, declared, uf_table, memo, term)?);
        }
        Some(values)
    }

    /// Asserted UNIT-EQUALITY pins on adoptable-UF applications:
    /// `(app, partner)` pairs from top-level ground assertions of the shape
    /// `(= (g t⃗) rhs)` / `(= lhs (g t⃗))` (binary `=` only, descending
    /// through top-level `and` conjuncts), where `g` is an adoptable head.
    /// Each pair seeds the constructed table with `(g, eval(t⃗)) :=
    /// eval(partner)` — the exact value the assertion forces at that point,
    /// so the seed is the only choice with a chance of surviving the final
    /// re-evaluation (which remains the sole authority; a conflicting or
    /// merely wrong seed can only produce a decline, never a wrong grant).
    fn left_inverse_unit_equalities(
        &self,
        ground_assertions: &[TermId],
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
    ) -> Vec<(TermId, TermId)> {
        let mut pins: Vec<(TermId, TermId)> = Vec::new();
        let mut stack: Vec<TermId> = ground_assertions.iter().rev().copied().collect();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(assertion) = stack.pop() {
            if !visited.insert(assertion) {
                continue;
            }
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            match sym.name() {
                "and" => stack.extend(args.iter().rev().copied()),
                "=" if args.len() == 2 => {
                    for (side, partner) in [(args[0], args[1]), (args[1], args[0])] {
                        let TermData::App(head, _) = self.ctx.terms.get(side) else {
                            continue;
                        };
                        if self.li_symbol_is_adoptable_uf(head, roles, declared) {
                            pins.push((side, partner));
                        }
                    }
                }
                _ => {}
            }
        }
        pins
    }

    /// The CLOSED (bound-variable-free) disjuncts of a forall whose body is
    /// an `or` — the candidate dominating disjuncts of the guarded-forall leg,
    /// and the roots the UF-graph adoption must cover so their applications
    /// have constructed-table values by evaluation time. Empty for any other
    /// body shape.
    fn left_inverse_closed_or_disjuncts(&self, quant: TermId) -> Vec<TermId> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return Vec::new();
        };
        let bound: HashSet<String> = vars.iter().map(|(name, _)| name.clone()).collect();
        let TermData::App(sym, args) = self.ctx.terms.get(*body) else {
            return Vec::new();
        };
        if sym.name() != "or" {
            return Vec::new();
        }
        args.iter()
            .copied()
            .filter(|&d| !self.term_contains_bound_var(d, &bound))
            .collect()
    }

    /// Collect (in deterministic first-visit order) every ground application
    /// term under `roots` whose symbol is ADOPTABLE — an unconstrained,
    /// user-DECLARED, non-Skolem, non-interpreted head (see
    /// [`Self::li_symbol_is_adoptable_uf`]). Quantifier subtrees are skipped:
    /// binder-dependent applications are not ground points (the guarded leg's
    /// closed disjuncts enter through their own roots).
    fn left_inverse_collect_adoptable_apps(
        &self,
        roots: &[TermId],
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
    ) -> Vec<TermId> {
        let mut collected: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if self.li_symbol_is_adoptable_uf(sym, roles, declared) {
                        collected.push(term);
                    }
                    stack.extend(args.iter().rev().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    stack.push(*else_term);
                    stack.push(*then_term);
                    stack.push(*cond);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    stack.extend(bindings.iter().rev().map(|(_, value)| *value));
                }
                // Binder-dependent occurrences are not ground points.
                TermData::Forall(..) | TermData::Exists(..) => {}
                _ => {}
            }
        }
        collected
    }

    /// Whether an application head may take a CONSTRUCTED-TABLE (adopted)
    /// interpretation: it must be genuinely uninterpreted — a user-DECLARED,
    /// non-Skolem symbol outside every role and every interpreted family.
    /// The positive `declared` requirement is the load-bearing guard: this set
    /// comes only from [`ay_frontend::CheckedProjectionBindings`], so every
    /// member is an exact live ordinary free-UF identity with a checked
    /// signature. Definitions, datatype members, theory declarations, solver
    /// internals, stale declarations, and raw core symbols are absent.
    fn li_symbol_is_adoptable_uf(
        &self,
        symbol: &Symbol,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
    ) -> bool {
        declared.contains(symbol)
            && !roles.contains_key(symbol)
            && !self.ctx.terms.is_skolem_symbol(symbol.name())
            && !is_pure_arith_bool_symbol(symbol.name())
            && !is_interpreted_bv_symbol(symbol.name())
    }

    /// Whether an application head delegates to the core evaluator as a PURE
    /// INTERPRETED operator (rebuilt over constant arguments): whitelisted
    /// linear-arith/Bool or BV operator, and NOT shadowed by a user
    /// declaration or Skolem (a UF named `bvfoo` must not ride the `bv*`
    /// prefix whitelist).
    fn li_symbol_is_delegable_interpreted(
        &self,
        symbol: &Symbol,
        declared: &HashSet<Symbol>,
    ) -> bool {
        Self::left_inverse_application_is_native(symbol)
            && !declared.contains(symbol)
            && !self.ctx.terms.is_skolem_symbol(symbol.name())
    }

    /// The ADOPTED value of one unconstrained-UF ground application: the
    /// extracted model's value for the application term, converted through
    /// the result-sort gate (Bool/BitVec/Int/Uninterpreted only — the sort
    /// gate is part of the soundness story: a head whose result sort has no
    /// [`LiValue`] representation can never be given a table point).
    /// `None` when the extraction is lossy at this term — the point is then
    /// only fillable through a sibling occurrence, or stays unfilled and
    /// declines whatever needs it.
    fn left_inverse_adopted_app_value(&self, model: &Model, app: TermId) -> Option<LiValue> {
        match self.ctx.terms.sort(app) {
            Sort::Bool | Sort::BitVec(_) | Sort::Int => {
                self.left_inverse_delegate_interpreted(model, app)
            }
            Sort::Uninterpreted(sort_name) => match self.evaluate_term(model, app) {
                EvalValue::Element(element) => {
                    Some(LiValue::Elem(LiElem::Extracted(sort_name.clone(), element)))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Scan the Bool/BitVec/linear-Int fragment while also allowing
    /// uninterpreted-sorted subterms (mod/div/nonlinear multiplication still
    /// decline). The left-inverse certificate necessarily works over
    /// ground cores containing uninterpreted-sorted (boxed) terms; their
    /// values are definite `Element`s under the EUF model, and every atom the
    /// certificate's argument depends on is directly checked for definite
    /// evaluation, so the sort restriction of the strict fragment adds
    /// nothing there.
    fn term_in_bv_bool_euf_lia_or_uninterpreted_fragment(&self, term: TermId) -> bool {
        let debug = ay_core::misc_cli_flags().debug_cert;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if !matches!(
                self.ctx.terms.sort(t),
                Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Uninterpreted(_)
            ) {
                if debug {
                    eprintln!(
                        "CERT/left-inverse: fragment reject {t:?} sort={:?} data={:?}",
                        self.ctx.terms.sort(t),
                        self.ctx.terms.get(t),
                    );
                }
                return false;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if is_pure_arith_bool_symbol(sym.name())
                        && !is_evaluable_linear_symbol(sym.name())
                    {
                        if debug {
                            eprintln!("CERT/left-inverse: fragment reject {t:?} op={}", sym.name());
                        }
                        return false;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return false,
            }
        }
        true
    }

    /// Positively authenticate every application head whose interpretation the
    /// left-inverse construction is allowed to choose.
    ///
    /// Request discovery is intentionally syntactic, while authority is not:
    /// each discovered exact core [`Symbol`] and complete signature is handed to
    /// the frontend's declaration checker against the complete authored root
    /// graph.  Consequently a fixed-semantics, undeclared, stale, overloaded,
    /// indexed, internal, or signature-inconsistent head sinks the whole
    /// certificate instead of being reclassified by spelling.
    fn left_inverse_checked_projection_bindings(
        &self,
        roots: &[TermId],
    ) -> Option<ay_frontend::CheckedProjectionBindings> {
        const MAX_LEFT_INVERSE_BINDING_TERMS: usize = 1_000_000;

        if roots.is_empty() || self.external_stop_reason().is_some() {
            return None;
        }
        let mut signatures: HashMap<Symbol, (Vec<Sort>, Sort)> = HashMap::default();
        let mut request_order: Vec<Symbol> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_LEFT_INVERSE_BINDING_TERMS
                || term.index() >= self.ctx.terms.len()
                || self.external_stop_reason().is_some()
            {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    if !Self::left_inverse_application_is_native(symbol) {
                        let parameter_sorts: Vec<Sort> = args
                            .iter()
                            .map(|&arg| self.ctx.terms.sort(arg).clone())
                            .collect();
                        let result_sort = self.ctx.terms.sort(term).clone();
                        if let Some((prior_parameters, prior_result)) = signatures.get(symbol) {
                            if prior_parameters != &parameter_sorts || prior_result != &result_sort
                            {
                                return None;
                            }
                        } else {
                            request_order.push(symbol.clone());
                            signatures.insert(symbol.clone(), (parameter_sorts, result_sort));
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return None,
            }
        }
        if request_order.is_empty() {
            return None;
        }
        let requests: Vec<ay_frontend::ProjectionBindingRequest> = request_order
            .into_iter()
            .map(|symbol| {
                let (parameter_sorts, result_sort) = signatures.remove(&symbol)?;
                Some(ay_frontend::ProjectionBindingRequest {
                    symbol,
                    parameter_sorts,
                    result_sort,
                })
            })
            .collect::<Option<_>>()?;
        self.ctx.check_projection_bindings(roots, &requests).ok()
    }

    /// Whether one exact core symbol is interpreted natively by the
    /// left-inverse evaluator. Indexed symbols qualify only for the established
    /// indexed-BV operator family; an arbitrary indexed base spelling never
    /// inherits the broader named arithmetic/Boolean whitelist.
    fn left_inverse_application_is_native(symbol: &Symbol) -> bool {
        match symbol {
            Symbol::Named(name) => {
                is_evaluable_linear_symbol(name) || is_interpreted_bv_symbol(name)
            }
            Symbol::Indexed(name, _) => is_interpreted_bv_symbol(name),
            _ => false,
        }
    }

    /// Recognize `forall x:S. (= (f x) x)` (either equality orientation):
    /// single binder, `f` a non-Skolem uninterpreted unary symbol applied
    /// exactly to the bound variable. `f := id` materializes over ANY
    /// (enlarged) universe, so the shape is universe-independent once its
    /// ground applications are verified to agree with the model.
    fn unary_identity_definition_symbol(&self, quant: TermId) -> Option<Symbol> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return None;
        };
        let [(var_name, binder_sort)] = vars.as_slice() else {
            return None;
        };
        let TermData::App(eq, sides) = self.ctx.terms.get(*body) else {
            return None;
        };
        if eq.name() != "=" || sides.len() != 2 {
            return None;
        }
        let recognize = |lhs: TermId, rhs: TermId| -> Option<Symbol> {
            let TermData::Var(rhs_name, _) = self.ctx.terms.get(rhs) else {
                return None;
            };
            if rhs_name != var_name {
                return None;
            }
            let TermData::App(f, f_args) = self.ctx.terms.get(lhs) else {
                return None;
            };
            let [arg] = f_args.as_slice() else {
                return None;
            };
            let TermData::Var(arg_name, _) = self.ctx.terms.get(*arg) else {
                return None;
            };
            if arg_name != var_name {
                return None;
            }
            if self.ctx.terms.sort(rhs) != binder_sort
                || self.ctx.terms.sort(*arg) != binder_sort
                || self.ctx.terms.sort(lhs) != binder_sort
            {
                return None;
            }
            let name = f.name();
            if is_pure_arith_bool_symbol(name)
                || is_interpreted_bv_symbol(name)
                || self.ctx.terms.is_skolem_symbol(name)
            {
                return None;
            }
            Some(f.clone())
        };
        recognize(sides[0], sides[1]).or_else(|| recognize(sides[1], sides[0]))
    }

    /// Recognize `forall x:S. (= (Unbox (Box x)) x)` (either equality
    /// orientation): single binder, unary application chain applied exactly to
    /// the bound variable, `Box`/`Unbox` distinct non-Skolem uninterpreted
    /// symbols, and `Box`'s result sort uninterpreted (so its universe can be
    /// enlarged at will in the construction argument). Returns
    /// `(box, unbox, S)` — the binder sort `S` is also `Unbox`'s result sort
    /// (fixed by well-sortedness of the body), which the materialized `Unbox`
    /// needs for its off-image fallback value.
    fn left_inverse_axiom_symbols(&self, quant: TermId) -> Option<(Symbol, Symbol, Sort)> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return None;
        };
        let [(var_name, binder_sort)] = vars.as_slice() else {
            return None;
        };
        let TermData::App(eq, sides) = self.ctx.terms.get(*body) else {
            return None;
        };
        if eq.name() != "=" || sides.len() != 2 {
            return None;
        }
        let recognize = |lhs: TermId, rhs: TermId| -> Option<(Symbol, Symbol, Sort)> {
            let TermData::Var(rhs_name, _) = self.ctx.terms.get(rhs) else {
                return None;
            };
            if rhs_name != var_name {
                return None;
            }
            let TermData::App(unbox, unbox_args) = self.ctx.terms.get(lhs) else {
                return None;
            };
            let [inner] = unbox_args.as_slice() else {
                return None;
            };
            let TermData::App(box_sym, box_args) = self.ctx.terms.get(*inner) else {
                return None;
            };
            let [box_arg] = box_args.as_slice() else {
                return None;
            };
            let TermData::Var(arg_name, _) = self.ctx.terms.get(*box_arg) else {
                return None;
            };
            if arg_name != var_name {
                return None;
            }
            if self.ctx.terms.sort(rhs) != binder_sort
                || self.ctx.terms.sort(*box_arg) != binder_sort
                || self.ctx.terms.sort(lhs) != binder_sort
            {
                return None;
            }
            let box_name = box_sym.name();
            let unbox_name = unbox.name();
            if box_sym == unbox
                || is_pure_arith_bool_symbol(box_name)
                || is_interpreted_bv_symbol(box_name)
                || is_pure_arith_bool_symbol(unbox_name)
                || is_interpreted_bv_symbol(unbox_name)
                || self.ctx.terms.is_skolem_symbol(box_name)
                || self.ctx.terms.is_skolem_symbol(unbox_name)
            {
                return None;
            }
            // SOUNDNESS (#left-inverse-datatype-codomain): the whole
            // construction rests on `Box`'s codomain being ENLARGEABLE — the
            // materialization mints one fresh `BoxPoint` per domain point and
            // needs the universe to accommodate all of them. A `declare-
            // datatypes` sort surfaces as `Sort::Uninterpreted(name)` (see
            // `binder_sort_is_datatype`), but its carrier is FIXED by its
            // constructors and admits no fresh elements, so the bare
            // `Sort::Uninterpreted` test is not the property this needs.
            //
            // Without the datatype exclusion the certificate accepts a
            // left-inverse axiom whose codomain is FINITE, and an injection
            // from an infinite domain into a finite carrier does not exist:
            //
            //   (declare-datatypes ((C 0)) (((c1) (c2))))
            //   (declare-fun bx (Int) C) (declare-fun ubx (C) Int)
            //   (assert (forall ((a Int)) (= (ubx (bx a)) a)))
            //
            // is UNSAT by pigeonhole (z3 agrees), and the certificate GRANTED
            // it — measured at 608020b1ad, where the wrong `sat` was masked
            // only by a downstream consumer declining. Masking is not a
            // guarantee; the same certificate feeds paths that do publish.
            //
            // The three sibling gates already carry this exclusion
            // (`mbqi.rs:1230`, `:2061`, `:2178`, the last with the same
            // rationale in prose). This one was missed.
            let inner_sort = self.ctx.terms.sort(*inner);
            if !matches!(inner_sort, Sort::Uninterpreted(_))
                || self.binder_sort_is_datatype(inner_sort)
            {
                return None;
            }
            Some((box_sym.clone(), unbox.clone(), binder_sort.clone()))
        };
        recognize(sides[0], sides[1]).or_else(|| recognize(sides[1], sides[0]))
    }

    /// Memoized entry point of the left-inverse certificate's FUNCTIONALIZED
    /// RE-EVALUATOR: the value of ground `term` in the explicitly constructed
    /// model `M'` of [`Self::mbqi_sat_validated_left_inverse_axioms`], or
    /// `None` when `M'` does not pin a definite value (callers must fail
    /// closed on `None`).
    ///
    /// The evaluator interprets:
    /// - constrained heads by their MATERIALIZED interpretations (`roles`) —
    ///   never by the extracted model's lossy tables/per-term values;
    /// - free constants by ADOPTING the extracted model's assignment (a free
    ///   choice of `M'`: a per-variable value is trivially functional, and
    ///   every assertion is re-checked under it — nothing lossy is trusted);
    /// - Boolean structure natively (Kleene short-circuits are sound: every
    ///   term DENOTES in `M'`, so a definitely-false conjunct falsifies the
    ///   conjunction regardless of undetermined siblings);
    /// - pure interpreted operators by rebuilding the application over
    ///   CONSTANT argument terms and delegating to the core evaluator
    ///   (operator semantics on constants are model-independent);
    /// - everything else (unconstrained UF applications, unsupported
    ///   operators/sorts, binders) as `None`.
    ///
    /// `memo` must be scoped to one certificate run AND one `uf_table` state
    /// (one `model`, one `roles` registry): values are pure functions of
    /// `(model, roles, uf_table, term)` — the adoption fixpoint therefore
    /// uses a fresh memo per attempt.
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_reeval(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        term: TermId,
    ) -> Option<LiValue> {
        if let Some(cached) = memo.get(&term) {
            return cached.clone();
        }
        // Stack safety on deeply nested terms, same discipline as the core
        // evaluator (#4602).
        let value = stacker::maybe_grow(
            super::model::EVAL_STACK_RED_ZONE,
            super::model::EVAL_STACK_SIZE,
            || self.left_inverse_reeval_uncached(model, roles, declared, uf_table, memo, term),
        );
        memo.insert(term, value.clone());
        value
    }

    /// [`Self::left_inverse_reeval`] without the memo lookup/insert.
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_reeval_uncached(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        term: TermId,
    ) -> Option<LiValue> {
        let data = self.ctx.terms.get(term).clone();
        match data {
            // A constant's value is model-independent — delegate.
            TermData::Const(_) => self.left_inverse_delegate_interpreted(model, term),
            // Free constant: adopt the extracted assignment (see the entry
            // point's soundness note). A missing/indefinite value declines.
            TermData::Var(_, _) => match self.ctx.terms.sort(term).clone() {
                Sort::Bool | Sort::BitVec(_) | Sort::Int => {
                    self.left_inverse_delegate_interpreted(model, term)
                }
                Sort::Uninterpreted(sort_name) => match self.evaluate_term(model, term) {
                    EvalValue::Element(element) => {
                        Some(LiValue::Elem(LiElem::Extracted(sort_name, element)))
                    }
                    _ => None,
                },
                _ => None,
            },
            TermData::Not(inner) => {
                match self.left_inverse_reeval(model, roles, declared, uf_table, memo, inner)? {
                    LiValue::Bool(b) => Some(LiValue::Bool(!b)),
                    _ => None,
                }
            }
            TermData::Ite(cond, then_term, else_term) => self.left_inverse_reeval_ite(
                model, roles, declared, uf_table, memo, cond, then_term, else_term,
            ),
            TermData::App(sym, args) => self
                .left_inverse_reeval_app(model, roles, declared, uf_table, memo, term, sym, &args),
            // `Let` is expanded before assertions reach the solver; a survivor
            // would need a binding environment this evaluator does not carry.
            // Binders are never ground values. Fail closed on all of them and
            // on any future `TermData` variant (`#[non_exhaustive]`).
            _ => None,
        }
    }

    /// Application case of [`Self::left_inverse_reeval`]. `term` is the
    /// original application node (its sort keys the rebuilt delegation).
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_reeval_app(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        term: TermId,
        sym: Symbol,
        args: &[TermId],
    ) -> Option<LiValue> {
        let name = sym.name().to_string();
        // Constrained heads: the materialized interpretation is the ONLY
        // authority (premise 2 guarantees one role per symbol).
        if let Some(role) = roles.get(&sym).cloned() {
            let [arg] = args else {
                // A constrained head is unary by its axiom's shape; any other
                // arity cannot occur for the same symbol (one signature per
                // symbol) — decline defensively rather than reason about it.
                return None;
            };
            let value = self.left_inverse_reeval(model, roles, declared, uf_table, memo, *arg)?;
            return match role {
                // Box: total injective embedding, one universe element per
                // definite argument value. Structural equality of `BoxPoint`s
                // IS both injectivity and congruence.
                LiRole::Box => Some(LiValue::Elem(LiElem::BoxPoint(
                    sym.clone(),
                    Box::new(value),
                ))),
                // Identity head: f := id.
                LiRole::Identity => Some(value),
                // Unbox: inverse of the partner Box on its BoxPoint family,
                // designated fallback everywhere else (total by construction).
                LiRole::Unbox {
                    box_sym,
                    result_sort,
                } => match value {
                    LiValue::Elem(LiElem::BoxPoint(b, inner)) if b == box_sym => Some(*inner),
                    _ => self.left_inverse_fallback(&result_sort),
                },
            };
        }
        match name.as_str() {
            "true" if args.is_empty() => Some(LiValue::Bool(true)),
            "false" if args.is_empty() => Some(LiValue::Bool(false)),
            // Equality/distinct natively: structural `LiValue` equality is
            // exact value equality in `M'` (see the `LiElem` construction).
            "=" if args.len() >= 2 => {
                let mut values = Vec::with_capacity(args.len());
                for &arg in args {
                    values.push(
                        self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg)?,
                    );
                }
                Some(LiValue::Bool(values.windows(2).all(|w| w[0] == w[1])))
            }
            "distinct" if args.len() >= 2 => {
                let mut values = Vec::with_capacity(args.len());
                for &arg in args {
                    values.push(
                        self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg)?,
                    );
                }
                let mut all_distinct = true;
                for i in 0..values.len() {
                    for j in (i + 1)..values.len() {
                        if values[i] == values[j] {
                            all_distinct = false;
                        }
                    }
                }
                Some(LiValue::Bool(all_distinct))
            }
            // Kleene connectives: a definite dominator decides even when a
            // sibling stays undetermined (it still denotes SOME value in M').
            "and" => {
                let mut undetermined = false;
                for &arg in args {
                    match self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg) {
                        Some(LiValue::Bool(false)) => return Some(LiValue::Bool(false)),
                        Some(LiValue::Bool(true)) => {}
                        _ => undetermined = true,
                    }
                }
                if undetermined {
                    None
                } else {
                    Some(LiValue::Bool(true))
                }
            }
            "or" => {
                let mut undetermined = false;
                for &arg in args {
                    match self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg) {
                        Some(LiValue::Bool(true)) => return Some(LiValue::Bool(true)),
                        Some(LiValue::Bool(false)) => {}
                        _ => undetermined = true,
                    }
                }
                if undetermined {
                    None
                } else {
                    Some(LiValue::Bool(false))
                }
            }
            "not" if args.len() == 1 => {
                match self.left_inverse_reeval(model, roles, declared, uf_table, memo, args[0])? {
                    LiValue::Bool(b) => Some(LiValue::Bool(!b)),
                    _ => None,
                }
            }
            // Right-chained n-ary implication: false iff every antecedent is
            // true and the final consequent is false.
            "=>" if args.len() >= 2 => {
                let mut undetermined = false;
                for &arg in &args[..args.len() - 1] {
                    match self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg) {
                        Some(LiValue::Bool(false)) => return Some(LiValue::Bool(true)),
                        Some(LiValue::Bool(true)) => {}
                        _ => undetermined = true,
                    }
                }
                match self.left_inverse_reeval(
                    model,
                    roles,
                    declared,
                    uf_table,
                    memo,
                    args[args.len() - 1],
                ) {
                    Some(LiValue::Bool(true)) => Some(LiValue::Bool(true)),
                    Some(LiValue::Bool(false)) if !undetermined => Some(LiValue::Bool(false)),
                    _ => None,
                }
            }
            "xor" if !args.is_empty() => {
                let mut acc = false;
                for &arg in args {
                    match self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg)? {
                        LiValue::Bool(b) => acc ^= b,
                        _ => return None,
                    }
                }
                Some(LiValue::Bool(acc))
            }
            "ite" if args.len() == 3 => self.left_inverse_reeval_ite(
                model, roles, declared, uf_table, memo, args[0], args[1], args[2],
            ),
            _ => {
                if self.li_symbol_is_delegable_interpreted(&sym, declared) {
                    // Pure interpreted operator over definite interpreted
                    // argument values: rebuild over constant terms and
                    // delegate — the core evaluator's operator semantics on
                    // constants are model-independent, so no lossy model data
                    // is consulted.
                    let mut const_args = Vec::with_capacity(args.len());
                    for &arg in args {
                        let const_id = match self
                            .left_inverse_reeval(model, roles, declared, uf_table, memo, arg)?
                        {
                            LiValue::Bool(b) => self.ctx.terms.mk_bool(b),
                            LiValue::BitVec { value, width } => {
                                self.ctx.terms.mk_bitvec(value, width)
                            }
                            LiValue::Int(v) => self.ctx.terms.mk_int(v),
                            // An interpreted operator cannot take an
                            // uninterpreted-sorted argument ("=", "distinct",
                            // "ite" are handled above).
                            LiValue::Elem(_) => return None,
                        };
                        const_args.push(const_id);
                    }
                    let sort = self.ctx.terms.sort(term).clone();
                    let rebuilt = self.ctx.terms.mk_app(sym, &const_args, sort);
                    self.left_inverse_delegate_interpreted(model, rebuilt)
                } else if self.li_symbol_is_adoptable_uf(&sym, roles, declared) {
                    // Unconstrained user-declared UF: read the CONSTRUCTED
                    // functional table at the M'-valued point — NEVER the
                    // extracted per-term value directly (a per-term read
                    // without the one-entry-per-point guarantee is the
                    // non-functional #8969-style trap). A point the adoption
                    // fixpoint could not fill declines.
                    let mut arg_values = Vec::with_capacity(args.len());
                    for &arg in args {
                        arg_values.push(
                            self.left_inverse_reeval(model, roles, declared, uf_table, memo, arg)?,
                        );
                    }
                    uf_table.get(&(sym, arg_values)).cloned()
                } else {
                    // Neither materialized, native, delegable, nor adoptable
                    // (theory operators outside the whitelist, Skolems,
                    // reserved symbols, …) — fail closed.
                    None
                }
            }
        }
    }

    /// `ite` evaluation for [`Self::left_inverse_reeval`]: a definite
    /// condition selects its branch; an undetermined condition still pins the
    /// `ite` when BOTH branches agree on a definite value (the condition
    /// denotes SOME Bool in `M'`, so either branch choice yields that value).
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_reeval_ite(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> Option<LiValue> {
        match self.left_inverse_reeval(model, roles, declared, uf_table, memo, cond) {
            Some(LiValue::Bool(true)) => {
                self.left_inverse_reeval(model, roles, declared, uf_table, memo, then_term)
            }
            Some(LiValue::Bool(false)) => {
                self.left_inverse_reeval(model, roles, declared, uf_table, memo, else_term)
            }
            _ => {
                let then_value =
                    self.left_inverse_reeval(model, roles, declared, uf_table, memo, then_term)?;
                let else_value =
                    self.left_inverse_reeval(model, roles, declared, uf_table, memo, else_term)?;
                if then_value == else_value {
                    Some(then_value)
                } else {
                    None
                }
            }
        }
    }

    /// Delegate a PURE INTERPRETED ground term to the core evaluator and
    /// convert its definite value. Only Bool/BitVec/Int-sorted terms qualify;
    /// anything indefinite (including a non-integer rational on an Int-sorted
    /// term) declines. Callers guarantee the term contains no constrained
    /// head and no UF application (constants, model-assigned free variables,
    /// and rebuilt constant-argument operator applications), so the value
    /// depends only on adopted assignments and operator semantics — never on
    /// the lossy parts of the extraction.
    fn left_inverse_delegate_interpreted(&self, model: &Model, term: TermId) -> Option<LiValue> {
        match self.ctx.terms.sort(term) {
            Sort::Bool => match self.evaluate_term(model, term) {
                EvalValue::Bool(b) => Some(LiValue::Bool(b)),
                _ => None,
            },
            Sort::BitVec(_) => match self.evaluate_term(model, term) {
                EvalValue::BitVec { value, width } => Some(LiValue::BitVec { value, width }),
                _ => None,
            },
            Sort::Int => match self.evaluate_term(model, term) {
                EvalValue::Rational(r) if r.is_integer() => Some(LiValue::Int(r.numer().clone())),
                _ => None,
            },
            _ => None,
        }
    }

    /// The designated OFF-IMAGE fallback value a materialized `Unbox` takes
    /// outside its partner's `BoxPoint` family: an arbitrary but FIXED value
    /// of the result sort (any choice yields a well-defined total function;
    /// assertions constraining off-image points are re-checked against this
    /// exact choice). Sorts without a designated value decline.
    fn left_inverse_fallback(&self, sort: &Sort) -> Option<LiValue> {
        match sort {
            Sort::Bool => Some(LiValue::Bool(false)),
            Sort::Int => Some(LiValue::Int(num_bigint::BigInt::ZERO)),
            Sort::BitVec(bv_sort) => Some(LiValue::BitVec {
                value: num_bigint::BigInt::ZERO,
                width: bv_sort.width,
            }),
            // The per-sort padding element of the constructed universe —
            // distinct from every BoxPoint and every adopted element.
            Sort::Uninterpreted(name) => Some(LiValue::Elem(LiElem::Fallback(name.clone()))),
            _ => None,
        }
    }

    /// Whether `quant` (a skipped forall that is neither a left-inverse axiom
    /// nor an identity definition) holds in the constructed model `M'` by
    /// OR-DOMINATION: its body is a disjunction with at least one CLOSED
    /// disjunct (no bound variable) that re-evaluates to definite `true`
    /// under the materialized interpretation. Truth under the extracted model
    /// alone is insufficient because `M'` reinterprets the constrained heads.
    /// Note the disjunct MAY mention
    /// constrained heads (it is evaluated under their materialized
    /// interpretations) and the other disjuncts may mention anything (the
    /// true closed disjunct dominates for every binder value over any
    /// universe).
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_guarded_forall_holds(
        &mut self,
        model: &Model,
        roles: &HashMap<Symbol, LiRole>,
        declared: &HashSet<Symbol>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        quant: TermId,
    ) -> bool {
        let disjuncts = self.left_inverse_closed_or_disjuncts(quant);
        disjuncts.into_iter().any(|disjunct| {
            self.left_inverse_reeval(model, roles, declared, uf_table, memo, disjunct)
                == Some(LiValue::Bool(true))
        })
    }

    /// SOUND finite-domain MBQI SAT validation (#mbqi-completeness Q2 / EPR).
    ///
    /// Returns `Some(())` only when every binder ranges over a finite
    /// uninterpreted universe generated solely by ground constants and every
    /// cross-product instance evaluates to definite `Bool(true)` in the model.
    /// Any missing universe element or unevaluable instance fails closed.
    pub(in crate::executor) fn mbqi_sat_validated_finite_uninterpreted_domain(
        &mut self,
        snapshot: &[TermId],
        forall_quants: &[TermId],
    ) -> Option<CheckedMbqiSatAuthority> {
        if forall_quants.is_empty() {
            return None;
        }
        self.last_model.as_ref()?;

        // The certificate must cover the complete original quantified
        // snapshot, not merely the stripped ground window used by MBQI. Every
        // quantified assertion must be one of the direct forall roots supplied
        // for certification, and nested quantifiers are outside this fragment.
        let cert_set: HashSet<TermId> = forall_quants.iter().copied().collect();
        if forall_quants.iter().any(|q| !snapshot.contains(q)) {
            return None;
        }
        for &assertion in snapshot {
            if !contains_quantifier(&self.ctx.terms, assertion) {
                continue;
            }
            let TermData::Forall(_, body, _) = self.ctx.terms.get(assertion) else {
                return None;
            };
            if !cert_set.contains(&assertion) || contains_quantifier(&self.ctx.terms, *body) {
                return None;
            }
        }

        // 1. Every bound variable of every forall must range over an
        //    uninterpreted sort.
        let mut binder_sorts: HashSet<Sort> = HashSet::default();
        for &q in forall_quants {
            match self.ctx.terms.get(q) {
                TermData::Forall(vars, _, _) => {
                    if vars.is_empty() {
                        return None;
                    }
                    for (_, sort) in vars {
                        if !matches!(sort, Sort::Uninterpreted(_)) {
                            return None;
                        }
                        binder_sorts.insert(sort.clone());
                    }
                }
                _ => return None,
            }
        }

        // 2. Each binder sort's universe must be generated solely by ground
        //    constants - NO function application anywhere in the ORIGINAL
        //    snapshot may return that sort. Scanning only the stripped MBQI
        //    window misses generators that occur solely under a forall.
        if self.sort_universe_has_generating_function(snapshot, &binder_sorts) {
            return None;
        }

        // 3. Collect the GROUND terms of each binder sort: the full finite
        //    Herbrand universe (by step 2). Deliberately NO synthesized witnesses
        //    (a synthetic fresh element is not in the candidate model's domain, so
        //    the model assigns it no truth, breaking the check). The minimal-
        //    Herbrand model over the actual ground terms is a sound, complete SAT
        //    witness for the EPR fragment.
        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, snapshot);

        // 4. For each forall, instantiate at the FULL cross-product of its
        //    binders' universes; require every instance to be a definite
        //    Bool(true) under the model.
        for &q in forall_quants {
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => return None,
            };

            let mut universe_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
            for (_name, sort) in &vars {
                let mut seen: HashSet<TermId> = HashSet::default();
                let mut universe: Vec<TermId> = Vec::new();
                for &t in ground_by_sort.get(sort).into_iter().flatten() {
                    if seen.insert(t) {
                        universe.push(t);
                    }
                }
                // Empty universe: no ground term => domain not enumerable. Fail
                // closed rather than guess.
                if universe.is_empty() {
                    return None;
                }
                universe_per_var.push(universe);
            }

            let total: usize = universe_per_var
                .iter()
                .try_fold(1usize, |acc, u| acc.checked_mul(u.len()))?;
            if total > MAX_QUICK_CHECK_CANDIDATES {
                return None;
            }

            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let mut indices: Vec<usize> = vec![0; vars.len()];
            loop {
                let binding: Vec<TermId> = indices
                    .iter()
                    .enumerate()
                    .map(|(var_idx, &term_idx)| universe_per_var[var_idx][term_idx])
                    .collect();
                let subst_map: HashMap<String, TermId> = var_names
                    .iter()
                    .zip(binding.iter())
                    .map(|(name, &t)| (name.clone(), t))
                    .collect();
                let ground_body = subst_vars(&mut self.ctx.terms, body, &subst_map);

                // SOUNDNESS: require a DEFINITE Bool(true). No UF-completion
                // guessing here - the certificate must be exact.
                let model = self.last_model.as_ref()?;
                let eval = self.evaluate_term(model, ground_body);
                if !matches!(eval, EvalValue::Bool(true)) {
                    return None;
                }

                let mut carry = true;
                for i in (0..vars.len()).rev() {
                    if carry {
                        indices[i] += 1;
                        if indices[i] < universe_per_var[i].len() {
                            carry = false;
                        } else {
                            indices[i] = 0;
                        }
                    }
                }
                if carry {
                    break;
                }
            }
        }

        CheckedMbqiSatAuthority::for_current(self, snapshot)
    }

    /// Return `true` if any term in `assertions` is a function APPLICATION (an
    /// `App` with at least one argument) whose result sort is one of `sorts`.
    /// Such a symbol can generate domain elements beyond the ground constants,
    /// making the sort's Herbrand universe potentially infinite - so ground-term
    /// enumeration is NOT a complete cover of the sort.
    ///
    /// Equality / disequality are Boolean-valued, never return an uninterpreted
    /// sort, so they are naturally excluded by the result-sort test. A bare
    /// constant declared as (declare-fun a () U) is an `App` with ZERO args (or a
    /// `Var`/`Const`) and is correctly NOT counted.
    fn sort_universe_has_generating_function(
        &self,
        assertions: &[TermId],
        sorts: &HashSet<Sort>,
    ) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let TermData::App(_, args) = self.ctx.terms.get(t) {
                if !args.is_empty() && sorts.contains(self.ctx.terms.sort(t)) {
                    return true;
                }
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        false
    }

    // =====================================================================
    // (#p2-mbqi-empty-universe) c1: singleton-witness decide for foralls
    // over an EMPTY uninterpreted-sort universe — decides BOTH directions.
    // =====================================================================

    /// Recognize a snapshot whose root foralls bind ONLY uninterpreted sorts,
    /// where at least one bound sort has an EMPTY ground universe (no ground
    /// term of that sort anywhere): synthesize ONE fresh witness constant per
    /// empty sort (SMT-LIB sorts are nonempty), instantiate every certified
    /// forall over the full cross-product (singleton witness for empty sorts,
    /// the complete ground Herbrand universe otherwise), and decide the
    /// resulting QUANTIFIER-FREE consequence set.
    ///
    /// A SAT instance set is solved through the same-`Context` checked-model
    /// transport, then accepted only when the installed EUF carrier is exactly
    /// the enumerated representative set for every binder sort. A strict-proof
    /// UNSAT token remains a separate decision lane and is consumed
    /// immediately.
    ///
    /// REVIEW GUARDS (wavec-p2 revision):
    /// 1. Every certified body must be QUANTIFIER-FREE. A nested binder would
    ///    make the instance re-quantified: the sub-solver does not know
    ///    |U| = 1 and could satisfy `∃y:U. ¬p(y)` by inventing a second
    ///    element the singleton argument forbids (wrong-SAT), and a
    ///    quantified instance could re-enter this very pipeline.
    /// 2. Every snapshot assertion outside the certified roots must be
    ///    QUANTIFIER-FREE — so no quantifier binding the empty sort (or any
    ///    sort) hides under `or`/`not` outside the certified set, and the
    ///    sub-solve covers the ENTIRE snapshot, never a strict subset.
    pub(in crate::executor) fn mbqi_empty_universe_singleton_decide(
        &mut self,
        snapshot: &[TermId],
        forall_quants: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<SolveResult> {
        if forall_quants.is_empty() || self.external_stop_reason().is_some() {
            return None;
        }

        // 1. Class scan of the certified foralls (all binders uninterpreted,
        //    quantifier-free bodies, no `no_mbqi` markers).
        let cert_set: HashSet<TermId> = forall_quants.iter().copied().collect();
        let mut binder_sorts: HashSet<Sort> = HashSet::default();
        for &q in forall_quants {
            if self.ctx.terms.is_no_mbqi(q) {
                return None;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q) else {
                return None;
            };
            if vars.is_empty() || contains_quantifier(&self.ctx.terms, *body) {
                return None;
            }
            for (_, s) in vars {
                if !matches!(s, Sort::Uninterpreted(_)) {
                    return None;
                }
                binder_sorts.insert(s.clone());
            }
        }
        // Whole-snapshot class: certified roots must BE snapshot conjuncts,
        // and everything else must be quantifier-free (guard 2).
        let mut ground: Vec<TermId> = Vec::new();
        for &a in snapshot {
            if cert_set.contains(&a) {
                continue;
            }
            if contains_quantifier(&self.ctx.terms, a) {
                return None;
            }
            if !ground.contains(&a) {
                ground.push(a);
            }
        }
        if forall_quants.iter().any(|q| !snapshot.contains(q)) {
            return None;
        }

        // 2. No function application may return a binder sort: the ground
        //    constants (plus the synthesized witnesses) are the whole domain.
        let snapshot_vec: Vec<TermId> = snapshot.to_vec();
        if self.sort_universe_has_generating_function(&snapshot_vec, &binder_sorts) {
            return None;
        }

        // 3. Universe per binder sort; collect the EMPTY ones.
        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, &snapshot_vec);
        let mut empty_sort_names: HashSet<String> = HashSet::default();
        for s in &binder_sorts {
            if ground_by_sort.get(s).is_none_or(Vec::is_empty) {
                let Sort::Uninterpreted(name) = s else {
                    return None;
                };
                empty_sort_names.insert(name.clone());
            }
        }
        if empty_sort_names.is_empty() {
            // Fully-ground universes: the existing exact enumerating
            // certifier owns this configuration.
            return None;
        }

        // 4. Conservative occurrence scan: no term of an empty sort other
        //    than the certified binders themselves, and no term whose sort
        //    structurally mentions an empty sort (Array/Seq/DT smuggling),
        //    anywhere in the snapshot.
        for &a in snapshot {
            let (walk_root, allowed): (TermId, HashSet<String>) = match self.ctx.terms.get(a) {
                TermData::Forall(vars, body, _) if cert_set.contains(&a) => {
                    (*body, vars.iter().map(|(n, _)| n.clone()).collect())
                }
                _ => (a, HashSet::default()),
            };
            if !self.term_free_of_empty_sort_occurrences(walk_root, &empty_sort_names, &allowed) {
                return None;
            }
        }

        // 5. Synthesize one witness per empty sort and instantiate every
        //    certified forall over the full cross-product.
        let mut witnesses: HashMap<String, TermId> = HashMap::default();
        for name in &empty_sort_names {
            let u = self
                .ctx
                .terms
                .mk_fresh_var("ay_epr_u0", Sort::Uninterpreted(name.clone()));
            witnesses.insert(name.clone(), u);
        }
        let mut sub_assertions: Vec<TermId> = ground;
        for &q in forall_quants {
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => return None,
            };
            let mut universe_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
            for (_n, s) in &vars {
                let Sort::Uninterpreted(name) = s else {
                    return None;
                };
                if let Some(&u) = witnesses.get(name) {
                    universe_per_var.push(vec![u]);
                } else {
                    let mut seen: HashSet<TermId> = HashSet::default();
                    let mut universe: Vec<TermId> = Vec::new();
                    for &t in ground_by_sort.get(s).into_iter().flatten() {
                        if seen.insert(t) {
                            universe.push(t);
                        }
                    }
                    if universe.is_empty() {
                        return None;
                    }
                    universe_per_var.push(universe);
                }
            }
            let total: usize = universe_per_var
                .iter()
                .try_fold(1usize, |acc, u| acc.checked_mul(u.len()))?;
            if total > MAX_QUICK_CHECK_CANDIDATES {
                return None;
            }
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let mut indices: Vec<usize> = vec![0; vars.len()];
            loop {
                let subst_map: HashMap<String, TermId> = var_names
                    .iter()
                    .enumerate()
                    .map(|(i, n)| (n.clone(), universe_per_var[i][indices[i]]))
                    .collect();
                let inst = subst_vars(&mut self.ctx.terms, body, &subst_map);
                if !sub_assertions.contains(&inst) {
                    sub_assertions.push(inst);
                }
                let mut carry = true;
                for i in (0..indices.len()).rev() {
                    if carry {
                        indices[i] += 1;
                        if indices[i] < universe_per_var[i].len() {
                            carry = false;
                        } else {
                            indices[i] = 0;
                        }
                    }
                }
                if carry {
                    break;
                }
            }
        }
        if sub_assertions.is_empty() {
            return None;
        }

        let mut published = 0usize;
        let accepted = self.with_checked_same_context_ground_model(
            sub_assertions.clone(),
            2_000,
            |executor, instance_roots| {
                published = executor
                    .publish_singleton_universe_uf_tables(instance_roots, &empty_sort_names);
                Some(())
            },
            |executor, installed| {
                // The structural singleton theorem must describe the exact
                // emitted model, not merely some smaller model whose selected
                // witness rows happened to satisfy the instances. Every EUF
                // carrier element for a binder sort must be denoted by one of
                // the representatives used in the full cross-product.
                if !executor.singleton_carriers_are_exact(
                    &binder_sorts,
                    &witnesses,
                    &ground_by_sort,
                ) || !installed.consume(executor)
                {
                    return None;
                }
                let evidence = CheckedMbqiSatAuthority::for_current(executor, snapshot)?;
                executor.install_mbqi_sat_authority(evidence).then_some(())
            },
        );

        if accepted.is_some() {
            if published > 0 {
                self.last_statistics
                    .set_int("model_completion.singleton_universe_ufs", published as u64);
            }
            self.defer_model_validation = false;
            self.last_model_validated = true;
            self.last_unknown_reason = None;
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/empty-universe: checked singleton model SAT over exact carriers");
            }
            return Some(SolveResult::Sat);
        }

        match self.checked_ground_solve(sub_assertions.clone(), fallback_category, 2_000) {
            Some(CheckedGroundDecision::Unsat(checked)) => {
                if !checked.consume(self, &sub_assertions) {
                    return None;
                }
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/empty-universe: strict checked singleton-instance UNSAT");
                }
                Some(SolveResult::unsat())
            }
            Some(CheckedGroundDecision::Sat(checked)) => {
                let _declined = checked.consume(self, &sub_assertions);
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/empty-universe: checked model transport declined SAT");
                }
                None
            }
            _ => None,
        }
    }

    fn singleton_carriers_are_exact(
        &self,
        binder_sorts: &HashSet<Sort>,
        witnesses: &HashMap<String, TermId>,
        ground_by_sort: &HashMap<Sort, Vec<TermId>>,
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        let Some(euf) = model.euf_model.as_ref() else {
            return false;
        };

        for sort in binder_sorts {
            let Sort::Uninterpreted(name) = sort else {
                return false;
            };
            let representatives: Vec<TermId> = if let Some(&witness) = witnesses.get(name) {
                vec![witness]
            } else {
                let Some(representatives) = ground_by_sort.get(sort) else {
                    return false;
                };
                representatives.clone()
            };
            let Some(represented_elements) = representatives
                .iter()
                .map(|&term| match self.evaluate_term(model, term) {
                    EvalValue::Element(element) => Some(element),
                    _ => None,
                })
                .collect::<Option<HashSet<String>>>()
            else {
                return false;
            };
            let Some(carrier_elements) = euf.sort_elements.get(name) else {
                return false;
            };
            if carrier_elements.is_empty()
                || represented_elements != carrier_elements.iter().cloned().collect()
            {
                return false;
            }
        }
        true
    }

    /// Materialize into the ADOPTED sub-model the function interpretations the
    /// singleton-universe sub-solve actually decided (#eu-uf-interp).
    ///
    /// THE GAP THIS CLOSES. The doc on
    /// [`Self::mbqi_empty_universe_singleton_decide`] promises that the
    /// adopted sub-model "carries the finite universe incl. the witness and
    /// every UF value at it". For the BV lanes that promise was FALSE: they
    /// ACKERMANNIZE `f(u)` into a fresh bit-blasted term
    /// (`theories/bv_axioms_euf.rs`) and build no EUF function table, so the
    /// adopted `euf_model.function_tables` came back EMPTY even though
    /// `(get-value ((f u)))` answers from the bit-blasted assignment. Two
    /// consumers then read the silence as "no interpretation exists":
    /// `(get-model)`'s ground-application fallback OMITS the symbol (its
    /// scope limit refuses to publish a total `define-fun` for a symbol that
    /// occurs under a quantifier), and the quantified model-check gate's
    /// `quantified_gate_uf_interps` drops the head "(no table)", defers, and
    /// the deferral fails the `sat` CLOSED. The solver decided a value and
    /// threw it away; this publishes it.
    ///
    /// WHY THE PUBLISHED TABLE IS EXACT, NOT A COMPLETION DEFAULT. A symbol is
    /// published only when EVERY one of its argument sorts is an
    /// EMPTY-universe uninterpreted sort. The caller's guards 2 and 4 prove
    /// that such a sort has NO term anywhere in the snapshot other than the
    /// single witness this lane synthesized (no generating function returns
    /// it, no composite sort smuggles it in), so the sort's model domain is
    /// exactly that one element and the function's domain is exactly ONE
    /// point. The instance set applies the function AT that point, so the one
    /// row read back is a TOTAL interpretation — the printer's one-row body is
    /// the row's own value, never a fabricated sort default. Nothing is
    /// invented: the key is the model's own element token for the witness and
    /// the value is read back through the same `term_value_string` path
    /// `(get-value)` uses.
    ///
    /// FAIL-CLOSED EVERYWHERE. A symbol is skipped — leaving today's deferring
    /// behaviour exactly as it is — when it already has a table, is a
    /// conflicted/defined/internal symbol, has any argument outside the
    /// singleton domain, has an unreadable argument or result value, is
    /// applied at more than the single domain point, or disagrees with itself
    /// at one point (a congruence violation, never papered over). The pass
    /// only FILLS an `euf_model` the solve already built: it never creates
    /// one, because materializing an otherwise-absent EUF component would
    /// change the `euf_backed` evidence the downstream validation gates read.
    fn publish_singleton_universe_uf_tables(
        &mut self,
        instance_roots: &[TermId],
        empty_sort_names: &HashSet<String>,
    ) -> usize {
        let Some(mut model) = self.last_model.take() else {
            return 0;
        };
        if model.euf_model.is_none() {
            self.last_model = Some(model);
            return 0;
        }

        // Ground uninterpreted-function applications of the exact checked
        // instance roots. The same-Context probe has already restored the
        // outer assertion vector before this postprocessor runs.
        let mut apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> = HashMap::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        for &assertion in instance_roots {
            self.collect_uf_applications(assertion, &mut apps, &mut visited);
        }

        // Deterministic order: the model is a published artifact.
        let mut candidates: Vec<(String, Vec<Sort>)> = Vec::new();
        for (surface, info) in self.ctx.symbol_iter() {
            if info.arg_sorts.is_empty() {
                continue;
            }
            if self.ctx.is_defined_fun(surface) || self.ctx.is_internal_symbol(surface) {
                continue;
            }
            let identity = self.ctx.symbol_identity_name(surface, info);
            if self.is_exact_dt_internal_symbol(identity) {
                continue;
            }
            // Every argument must range over a synthesized singleton domain.
            if !info.arg_sorts.iter().all(|s| match s {
                Sort::Uninterpreted(name) => empty_sort_names.contains(name),
                _ => false,
            }) {
                continue;
            }
            candidates.push((identity.to_string(), info.arg_sorts.clone()));
        }
        candidates.sort();
        candidates.dedup();

        let mut published = 0usize;
        for (identity, arg_sorts) in candidates {
            let euf = model
                .euf_model
                .as_ref()
                .expect("euf component checked present above");
            if euf.function_tables.contains_key(&identity)
                || euf.function_table_conflicts.contains(&identity)
            {
                continue;
            }
            let Some(applications) = apps.get(&(identity.clone(), arg_sorts.len())) else {
                continue;
            };

            // Read every application back. `term_values` is EUF's own table
            // spelling (an `@Sort!n` element token, or a formatted scalar);
            // `term_value_string` is the `(get-value)` path. Either is a value
            // the model already commits to — neither invents one.
            let read_back = |exec: &Self, m: &Model, t: TermId| -> Option<String> {
                if let Some(v) = m
                    .euf_model
                    .as_ref()
                    .and_then(|e| e.term_values.get(&t))
                    .cloned()
                {
                    return Some(v);
                }
                exec.term_value_string(m, t).ok()
            };

            let mut rows: std::collections::BTreeMap<Vec<String>, String> =
                std::collections::BTreeMap::new();
            let mut usable = true;
            let mut source_terms: Vec<TermId> = Vec::new();
            for (app, args) in applications {
                let mut key = Vec::with_capacity(args.len());
                for &arg in args {
                    // The key must be the model's ELEMENT TOKEN for the
                    // witness; anything else is not a domain point this model
                    // names, so the row could not be checked against it.
                    match model
                        .euf_model
                        .as_ref()
                        .and_then(|e| e.term_values.get(&arg))
                        .cloned()
                    {
                        Some(token) if token.starts_with('@') => key.push(token),
                        _ => {
                            usable = false;
                            break;
                        }
                    }
                }
                if !usable {
                    break;
                }
                let Some(value) = read_back(self, &model, *app) else {
                    usable = false;
                    break;
                };
                match rows.get(&key) {
                    // Two applications at one domain point disagreeing is a
                    // congruence violation; publishing either would be a
                    // falsifying witness.
                    Some(prev) if *prev != value => {
                        usable = false;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        rows.insert(key, value);
                        source_terms.push(*app);
                    }
                }
            }
            // The domain is the cross-product of one witness per argument —
            // exactly one point. Anything else means the instance set did not
            // determine the function totally.
            if !usable || rows.len() != 1 {
                continue;
            }
            let euf = model
                .euf_model
                .as_mut()
                .expect("euf component checked present above");
            euf.function_tables.insert(
                identity.clone(),
                rows.into_iter().collect::<Vec<(Vec<String>, String)>>(),
            );
            euf.function_table_terms.insert(identity, source_terms);
            published += 1;
        }

        self.last_model = Some(model);
        published
    }

    /// `true` iff no subterm of `root` is of an empty binder sort (except a
    /// bare `Var` whose name is in `allowed_binder_names` — the certified
    /// forall's own binders) and no subterm's sort structurally MENTIONS one
    /// (arrays/sequences/datatypes over the sort would smuggle domain
    /// elements past the ground-universe scan).
    fn term_free_of_empty_sort_occurrences(
        &self,
        root: TermId,
        empty_sort_names: &HashSet<String>,
        allowed_binder_names: &HashSet<String>,
    ) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let sort = self.ctx.terms.sort(t);
            let is_allowed_binder = matches!(
                self.ctx.terms.get(t),
                TermData::Var(name, _) if allowed_binder_names.contains(name)
            );
            if !is_allowed_binder && sort_mentions_uninterpreted_names(sort, empty_sort_names) {
                return false;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        true
    }

    // =====================================================================
    // CAP-1: CERTIFIED SAT for the finite-table + default class (class A).
    // =====================================================================

    /// CERTIFIED SAT for quantified UFLIA problems in the conservative
    /// "finite-table + default" class (CAP-1 class A).
    ///
    /// # Certificate class (everything else returns `None` — fail closed)
    ///
    /// Every assertion in `snapshot` must be either
    /// - quantifier-free ("ground original"), or
    /// - a top-level `forall ((x Int)) B(x)` or `forall ((x Real)) B(x)` with
    ///   exactly ONE binder, where
    ///   every subterm of `B` is `Int`-, `Real`- or `Bool`-sorted, built from
    ///   the interpreted operators `and or not => xor ite = distinct < <= > >=
    ///   + - * to_real` (plus `/` restricted to literal NONZERO numeral
    ///   divisors — the only case whose semantics is fully pinned; any other
    ///   divisor rejects) plus uninterpreted applications that are either (a)
    ///   exactly `f(x)` — a unary free UF applied to the bare bound variable
    ///   ("table app"), with an `Int`, `Real` or `Bool` codomain — or (b)
    ///   applied to arguments that do not mention `x` at all ("ground UF
    ///   app"). Any occurrence of `x` inside a UF argument other than the
    ///   bare `f(x)` shape (e.g. `f(g(x))`, `f(x+1)`, `h(x,x)`) rejects the
    ///   certificate, as do `div mod abs`, unrestricted `/`, `Let`, nested
    ///   quantifiers, non-binder variables, and datatype
    ///   selectors/constructors.
    ///
    /// # Why a `Real` binder is in class (and where it must fail closed)
    ///
    /// The totality argument below splits the binder DOMAIN `D` (`Z` for an
    /// `Int` binder, `R` for a `Real` binder) into the finite table-point set
    /// `P` (checked pointwise, step 2) and its complement `D \ P` (covered by
    /// ONE residual check, step 3): pointwise table + default region = all of
    /// `D`. Neither leg enumerates `D`, so the argument is insensitive to
    /// whether `D` is countable or a continuum:
    ///
    /// - POINTWISE leg: `P` is finite by construction (one point per ground
    ///   application), and each point is an EXACT `BigRational` — over the
    ///   reals, ground-application arguments in the linear fragment evaluate
    ///   to rationals in AY models. An IRRATIONAL point value (an
    ///   `EvalValue::Algebraic` from an NRA-shaped ground part, e.g.
    ///   `c*c = 2 ∧ f(c) = 1`) has no exact `BigRational` key: the collect
    ///   step's `Rational`-only match arm rejects it and the certificate
    ///   fails closed. Rational points substitute into the exact evaluator
    ///   precisely like integer ones.
    /// - RESIDUAL leg: the fresh constant `k` carries the BINDER's sort, so
    ///   the ground refutation of `¬R(k) ∧ (k ≠ p)_{p ∈ P}` quantifies over
    ///   the SAME domain the binder ranges over — `Int`-sorted `k` for `Z`,
    ///   `Real`-sorted `k` for `R`. UNSAT of that formula is exactly
    ///   `∀ x ∈ D \ P. R(x)` valid under EVERY interpretation of the
    ///   remaining symbols: the continuum minus the finitely many excluded
    ///   points is covered wholesale by the solver's own real-arithmetic
    ///   reasoning, never by enumeration. No density or integrality
    ///   assumption enters anywhere.
    ///
    /// Two `Real`-binder-specific guards keep the trusted base identical to
    /// the `Int` path's:
    ///
    /// - LINEARITY: a `Real` binder additionally rejects any x-dependent
    ///   product whose shape is not `literal * x-dependent` (so `x*x`,
    ///   `f(x)*f(x)`, `g(c)*x` are all out of class). This keeps the
    ///   residual-leg probe inside linear real arithmetic (the fuzz-verified
    ///   QF_[UF]LRA lane) instead of leaning on an NRA UNSAT verdict, and
    ///   keeps ground-application points rational.
    /// - EXACT-RATIONAL VALUES: every table key and value must match
    ///   `EvalValue::Rational` / `Bool` exactly; `Algebraic` (and anything
    ///   else) fails closed, per the pointwise-leg note above.
    ///
    /// # The interpretation `M'` this function constructs
    ///
    /// Let `M` be the candidate model (`self.last_model`). For each table
    /// symbol `f`, collect EVERY ground application `f(t)` occurring anywhere
    /// in `snapshot` (ground assertions AND all forall bodies), and set
    ///
    /// ```text
    /// table_f = { eval_M(t) -> eval_M(f(t)) }        (reject on any Unknown
    ///                                                 or conflicting entries)
    /// M'(f)   = λc. if c ∈ dom(table_f) then table_f(c) else d_f
    /// ```
    ///
    /// for a chosen constant default `d_f` (bounded enumeration below). Every
    /// symbol other than the table symbols keeps its `M` interpretation.
    ///
    /// # Machine-checked totality argument (why `Some(())` implies SAT)
    ///
    /// 1. GROUND ORIGINALS. Each quantifier-free assertion is re-evaluated
    ///    under `M` and must be a definite `Bool(true)`. `M'` agrees with `M`
    ///    on every ground assertion: by construction `M'(f)` coincides with
    ///    `eval_M` at every ground application point of `f` occurring in the
    ///    snapshot (they are exactly the table entries), and all other symbols
    ///    are untouched, so the (compositional) evaluation of every
    ///    ground subterm is unchanged. Hence `M' ⊨ ground originals`.
    /// 2. FORALLS, table points. For each certified `forall x. B(x)` let `P` =
    ///    the union of `dom(table_f)` over the table symbols `f` with an
    ///    `f(x)` occurrence in `B`. For every point `c ∈ P` the body `B(c)` is
    ///    evaluated EXACTLY under `M'` by [`Self::finite_table_eval`] (bound
    ///    var ↦ `c`, table apps ↦ table/default lookup, x-free subterms ↦
    ///    `eval_M` = `eval_M'` by the same agreement argument as in 1) and
    ///    must be a definite `Bool(true)`.
    /// 3. FORALLS, default region. For every `c ∉ P`, every `f(x)` in `B`
    ///    evaluates to `d_f` under `M'`, so `B(c)` equals the RESIDUAL
    ///    `R(x) := B[f(x) := d_f]` at `x = c`. The residual is certified by
    ///    exactly one of:
    ///    - (a) `R` no longer mentions `x`: it is a ground term; require
    ///      `eval_M(R) = Bool(true)` (again `eval_M = eval_M'` on it);
    ///    - (b) `R` still mentions `x`: require an INDEPENDENT ground-solver
    ///      refutation of `¬R(k) ∧ (k ≠ p)_{p ∈ P}` for a fresh constant
    ///      `k` OF THE BINDER'S SORT
    ///      ([`Self::checked_ground_solve`]). UNSAT of that
    ///      formula is precisely `∀ x ∉ P. R(x)` valid under EVERY
    ///      interpretation of the remaining symbols — in particular `M'`.
    ///    Cases 2 and 3 cover all of the binder domain (`Z` or `R`), so
    ///    `M' ⊨ forall x. B(x)`.
    /// 4. Steps 1-3 hold SIMULTANEOUSLY (one shared `M'`, one shared default
    ///    vector across all assertions), so `M' ⊨ snapshot`. The snapshot is
    ///    the post-skolemization assertion set plus instantiation
    ///    consequences, so its satisfiability implies the original problem's.
    ///
    /// The trusted base is (i) the exact table evaluator over
    /// `BigInt`/`BigRational` (no machine-word overflow, no rounding), (ii)
    /// `evaluate_term`'s definite `Bool`/numeric verdicts under `M`, and
    /// (iii) the ground solver's UNSAT verdict in leg
    /// 3(b). Anything Unknown, out of fragment, out of budget, conflicting,
    /// or over-cap returns `None` and the caller keeps its fail-closed
    /// `Unknown`. This function only ever GRANTS a `Sat` certificate; it never
    /// produces or influences an UNSAT verdict.
    pub(in crate::executor) fn try_finite_table_sat_certificate(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<()> {
        use num_bigint::BigInt;

        let debug = ay_core::misc_cli_flags().debug_cert;
        let decline = |reason: &str| {
            if debug {
                eprintln!("CERT/finite-table: decline ({reason})");
            }
        };
        if debug {
            eprintln!(
                "CERT/finite-table: begin ({} roots, category={category:?})",
                snapshot.len()
            );
        }

        // Never extend a solve that is already past its deadline/interrupt.
        if self.external_stop_reason().is_some() {
            decline("external stop");
            return None;
        }
        // The ground solve may simplify every authored UF point equality away
        // before model extraction, leaving no retained candidate at all.  The
        // certificate constructs its own completed interpretation, so an empty
        // base is sufficient; every value it relies on is still checked below.
        let mut model = self.last_model.clone().unwrap_or_else(Model::empty);

        // ---- 1. Partition the snapshot; reject any non-top-level-forall
        //         quantifier occurrence (exists, Not(forall), nested, ...).
        let mut foralls: Vec<TermId> = Vec::new();
        let mut grounds: Vec<TermId> = Vec::new();
        for &a in snapshot {
            match self.ctx.terms.get(a) {
                TermData::Forall(..) => foralls.push(a),
                _ if contains_quantifier(&self.ctx.terms, a) => {
                    decline("non-top-level quantifier");
                    return None;
                }
                _ => grounds.push(a),
            }
        }
        if foralls.is_empty() {
            decline("no foralls");
            return None;
        }

        // ---- 2. Class-A shape scan of every forall.
        // Table symbol name -> codomain kind (Int / Bool / Real), plus the
        // exact argument sorts needed to materialize the certified M'.
        let mut table_syms: HashMap<String, TableCertSort> = HashMap::default();
        let mut table_arg_sorts: HashMap<String, Vec<Sort>> = HashMap::default();
        struct ForallInfo {
            var_name: String,
            var_sort: Sort,
            body: TermId,
            xdep: HashSet<TermId>,
            body_syms: Vec<String>,
        }
        let mut infos: Vec<ForallInfo> = Vec::with_capacity(foralls.len());
        for &q in &foralls {
            // A `no_mbqi` (E-matching-only, Hilbert-choose style) forall must
            // never be discharged by a model-based certificate.
            if self.ctx.terms.is_no_mbqi(q) {
                decline("no-mbqi forall");
                return None;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q) else {
                decline("root changed after partition");
                return None;
            };
            // Binder domain: `Int` or `Real` only (see the Real-binder doc
            // section for why the totality argument covers both).
            if vars.len() != 1 || !matches!(vars[0].1, Sort::Int | Sort::Real) {
                decline("unsupported binder shape or sort");
                return None;
            }
            let (var_name, var_sort, body) = (vars[0].0.clone(), vars[0].1.clone(), *body);
            let xdep = self.finite_table_xdep_nodes(body, &var_name);
            let mut body_syms: HashSet<String> = HashSet::default();
            if self
                .finite_table_scan_body(
                    body,
                    &var_name,
                    &var_sort,
                    &xdep,
                    &mut table_syms,
                    &mut table_arg_sorts,
                    &mut body_syms,
                )
                .is_none()
            {
                decline("forall body outside class-A fragment");
                return None;
            }
            let mut body_syms: Vec<String> = body_syms.into_iter().collect();
            body_syms.sort_unstable();
            infos.push(ForallInfo {
                var_name,
                var_sort,
                body,
                xdep,
                body_syms,
            });
        }

        // A spelling classifier is never authority to reinterpret a function.
        // Bind every selected head positively to one live ordinary free-UF
        // declaration, then audit every same-spelling occurrence and complete
        // signature across the authenticated snapshot.
        let mut checked_names: Vec<&String> = table_syms.keys().collect();
        checked_names.sort_unstable();
        let requests: Vec<ay_frontend::ProjectionBindingRequest> = checked_names
            .into_iter()
            .map(|name| {
                let result_sort = match table_syms[name] {
                    TableCertSort::Bool => Sort::Bool,
                    TableCertSort::Int => Sort::Int,
                    TableCertSort::Real => Sort::Real,
                };
                Some(ay_frontend::ProjectionBindingRequest {
                    symbol: Symbol::named(name),
                    parameter_sorts: table_arg_sorts.get(name)?.clone(),
                    result_sort,
                })
            })
            .collect::<Option<_>>()?;
        let Some(checked_table_bindings) =
            self.check_table_declaration_occurrences(snapshot, &requests)
        else {
            decline("table declaration identity/signature audit");
            return None;
        };

        // Re-materialize exact numeric UF pins from authored unit equalities.
        // Ground propagation is allowed to consume `(= (f c) k)`, but that
        // equality is itself authoritative model information. Installing only
        // its literal RHS into the disposable certificate model is therefore a
        // forced interpretation choice, not a guess; conflicting/congruent
        // points are still rejected by ground re-evaluation and table
        // collection below.
        {
            let euf = model.euf_model.get_or_insert_with(Default::default);
            for &ground in &grounds {
                let TermData::App(eq, args) = self.ctx.terms.get(ground) else {
                    continue;
                };
                if eq.name() != "=" || args.len() != 2 {
                    continue;
                }
                for (app, value) in [(args[0], args[1]), (args[1], args[0])] {
                    let TermData::App(sym, app_args) = self.ctx.terms.get(app) else {
                        continue;
                    };
                    if !table_syms.contains_key(sym.name())
                        || app_args.iter().any(|&arg| {
                            contains_quantifier(&self.ctx.terms, arg)
                                || matches!(self.ctx.terms.get(arg), TermData::Var(..))
                        })
                        || !matches!(self.ctx.terms.get(value), TermData::Const(_))
                        || !matches!(self.ctx.terms.sort(app), Sort::Int | Sort::Real)
                    {
                        continue;
                    }
                    euf.func_app_const_terms.insert(app, value);
                }
            }
        }
        super::model::eval_memo_clear();

        // ---- 3. Independent re-verification: M must make every ground
        //         original definitely true (no delegation, no completion
        //         guessing — a definite Bool(true) from the evaluator).
        for &g in &grounds {
            if !matches!(self.evaluate_term(&model, g), EvalValue::Bool(true)) {
                decline("ground assertion not definitely true in base model");
                return None;
            }
        }

        // ---- 4. Build the finite tables from EVERY ground application of a
        //         table symbol anywhere in the snapshot.
        let Some(tables) = self.finite_table_collect(&model, snapshot, &table_syms) else {
            decline("finite table collection");
            return None;
        };
        // `snapshot` is the exact pre-preprocessing solve obligation; do not
        // mix in the current working assertion window, which may contain
        // solver-generated residual/probe terms outside the certificate
        // fragment. Every authored ground point is already in `grounds`.
        let pin_roots = grounds.clone();
        let Some(ground_pins) = self.finite_table_ground_pins(&model, &pin_roots, &table_syms)
        else {
            decline("ground projection collection");
            return None;
        };

        // ---- 5. Bounded default-vector enumeration.
        let mut sym_names: Vec<String> = table_syms.keys().cloned().collect();
        sym_names.sort_unstable();
        // Int constants mentioned in forall bodies are good default hints
        // (e.g. `(or (>= x 0) (= (f x) -1))` wants d_f = -1).
        let mut body_consts: Vec<BigInt> = Vec::new();
        let mut body_rat_consts: Vec<num_rational::BigRational> = Vec::new();
        for info in &infos {
            self.finite_table_collect_int_consts(info.body, &mut body_consts);
            self.finite_table_collect_rat_consts(info.body, &mut body_rat_consts);
        }
        body_consts.sort();
        body_consts.dedup();
        body_consts.truncate(3);
        body_rat_consts.sort();
        body_rat_consts.dedup();
        body_rat_consts.truncate(3);
        let mut candidates_per_sym: Vec<Vec<TableCertVal>> = Vec::with_capacity(sym_names.len());
        for name in &sym_names {
            let codomain = *table_syms.get(name)?;
            let mut cands: Vec<TableCertVal> = Vec::new();
            match codomain {
                TableCertSort::Bool => {
                    cands.push(TableCertVal::Bool(false));
                    cands.push(TableCertVal::Bool(true));
                }
                TableCertSort::Int => {
                    let mut ints: Vec<BigInt> =
                        vec![BigInt::ZERO, BigInt::from(1), BigInt::from(-1)];
                    if let Some(table) = tables.get(name) {
                        let mut vals: Vec<BigInt> = table
                            .values()
                            .filter_map(|v| match v {
                                TableCertVal::Int(i) => Some(i.clone()),
                                TableCertVal::Bool(_) | TableCertVal::Rat(_) => None,
                            })
                            .collect();
                        vals.sort();
                        vals.dedup();
                        ints.extend(vals.into_iter().take(2));
                    }
                    ints.extend(body_consts.iter().cloned());
                    ints.dedup_by(|a, b| a == b); // adjacent only; full dedup below
                    let mut seen: HashSet<BigInt> = HashSet::default();
                    for v in ints {
                        if cands.len() >= MAX_TABLE_CERT_DEFAULTS_PER_SYM {
                            break;
                        }
                        if seen.insert(v.clone()) {
                            cands.push(TableCertVal::Int(v));
                        }
                    }
                }
                TableCertSort::Real => {
                    use num_rational::BigRational;
                    let mut rats: Vec<BigRational> = vec![
                        BigRational::from_integer(BigInt::ZERO),
                        BigRational::from_integer(BigInt::from(1)),
                        BigRational::from_integer(BigInt::from(-1)),
                    ];
                    if let Some(table) = tables.get(name) {
                        let mut vals: Vec<BigRational> = table
                            .values()
                            .filter_map(|v| match v {
                                TableCertVal::Rat(r) => Some(r.clone()),
                                TableCertVal::Int(_) | TableCertVal::Bool(_) => None,
                            })
                            .collect();
                        vals.sort();
                        vals.dedup();
                        rats.extend(vals.into_iter().take(2));
                    }
                    rats.extend(body_rat_consts.iter().cloned());
                    // Small list (<= 8): linear dedup preserves priority order.
                    let mut seen: Vec<BigRational> = Vec::new();
                    for v in rats {
                        if cands.len() >= MAX_TABLE_CERT_DEFAULTS_PER_SYM {
                            break;
                        }
                        if !seen.contains(&v) {
                            seen.push(v.clone());
                            cands.push(TableCertVal::Rat(v));
                        }
                    }
                }
            }
            candidates_per_sym.push(cands);
        }

        // Precompute per-forall table-point sets (union over the body's table
        // symbols) — these do not depend on the default vector. Points are
        // exact rationals (integer-valued for an `Int` binder).
        let mut points_per_forall: Vec<Vec<num_rational::BigRational>> =
            Vec::with_capacity(infos.len());
        for info in &infos {
            let mut points: Vec<num_rational::BigRational> = Vec::new();
            for name in &info.body_syms {
                if let Some(table) = tables.get(name) {
                    // CCMC M1: the pointwise leg checks the binder value at the
                    // point-component of EVERY table row (across all prefixes).
                    // Making `P` the union over all prefixes keeps the residual
                    // region `x ∉ P` valid for every prefix's default fallback
                    // (`(prefix_g, x) ∉ dom` whenever `x` is no row's point).
                    points.extend(table.keys().map(|(_prefix, point)| point.clone()));
                }
            }
            points.sort();
            points.dedup();
            if points.len() > MAX_TABLE_CERT_POINTS_TOTAL {
                return None;
            }
            points_per_forall.push(points);
        }

        // Mixed-radix enumeration of default vectors, capped.
        let mut solver_calls = 0usize;
        let mut combo_idx: Vec<usize> = vec![0; sym_names.len()];
        // A residual formula that already FAILED its ground-solver validity
        // check need not be re-solved for a later default vector that builds
        // the same residual term (hash-consed TermId equality).
        let mut failed_residuals: HashSet<TermId> = HashSet::default();
        let mut combo_count = 0usize;
        loop {
            combo_count += 1;
            if combo_count > MAX_TABLE_CERT_DEFAULT_COMBOS {
                return None;
            }
            let defaults: HashMap<String, TableCertVal> = sym_names
                .iter()
                .enumerate()
                .map(|(si, n)| (n.clone(), candidates_per_sym[si][combo_idx[si]].clone()))
                .collect();

            let Some(all_foralls_hold) = self.finite_table_check_all(
                &model,
                &infos
                    .iter()
                    .map(|i| {
                        (
                            i.var_name.as_str(),
                            &i.var_sort,
                            i.body,
                            &i.xdep,
                            i.body_syms.as_slice(),
                        )
                    })
                    .collect::<Vec<_>>(),
                &points_per_forall,
                &tables,
                &defaults,
                category,
                &mut solver_calls,
                &mut failed_residuals,
            ) else {
                decline("default-vector check stopped or exceeded its proof budget");
                return None;
            };
            if all_foralls_hold {
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!(
                        "CERT/finite-table: certified SAT ({} foralls, {} grounds, {} table syms, {} pins)",
                        infos.len(),
                        grounds.len(),
                        sym_names.len(),
                        ground_pins.len(),
                    );
                }
                // Residual validity checks are isolated nested solves and may
                // replace `last_model` with their temporary counterexample or
                // refutation model. The certificate, however, constructed M'
                // from this saved outer `model` and proved every ground
                // original agrees with it at all observed table points. Put
                // that model back before handing Sat to the public validation
                // funnel; otherwise ground applications can disappear and a
                // certified Sat is spuriously demoted to Unknown.
                let mut emitted_model = model.clone();
                let euf = emitted_model.euf_model.get_or_insert_with(Default::default);
                for (term, value) in &ground_pins {
                    let TermData::App(sym, _) = self.ctx.terms.get(*term) else {
                        continue;
                    };
                    if !table_syms.contains_key(sym.name()) {
                        continue;
                    }
                    let raw = match value {
                        EvalValue::Bool(value) => value.to_string(),
                        EvalValue::Rational(value) => {
                            crate::executor_format::format_rational(value)
                        }
                        _ => continue,
                    };
                    euf.term_values.insert(*term, raw);
                }
                // The certificate proves the TOTAL interpretation M', not
                // merely its observed ground projection. Publish that exact
                // structure: explicit rows first and the certified default as
                // the final (printer/evaluator else) row. Without this step an
                // all-quantifier formula such as `forall x. P(x)` could grant
                // Sat while parking an empty EUF model, and a table-plus-
                // default formula could print an unrelated sort default at an
                // unlisted point.
                self.install_finite_table_model(
                    &mut emitted_model,
                    &table_syms,
                    &table_arg_sorts,
                    &tables,
                    &defaults,
                    &checked_table_bindings,
                )?;
                emitted_model.install_quantified_certificate_pins(
                    &self.ctx.terms,
                    ground_pins.iter().cloned(),
                )?;
                // Park the exact checked model linearly. The public SAT funnel
                // moves it into `last_model` only after all nested probes have
                // finished; no clone can inherit or diverge from this witness.
                self.finite_table_cert_witness_state =
                    Some(FiniteTableWitnessState::pending_for_current_query(
                        self,
                        snapshot,
                        checked_table_bindings,
                        emitted_model,
                    )?);
                return Some(());
            }

            // Advance mixed-radix counter.
            let mut carry = true;
            for i in (0..combo_idx.len()).rev() {
                if carry {
                    combo_idx[i] += 1;
                    if combo_idx[i] < candidates_per_sym[i].len() {
                        carry = false;
                    } else {
                        combo_idx[i] = 0;
                    }
                }
            }
            if carry {
                decline("no shared default vector satisfies every forall");
                return None; // all combos exhausted
            }
        }
    }

    /// Capture exactly the ground applications whose interpretation is fixed
    /// by a finite-table certificate. Residual validity probes run as nested
    /// solves and can erase these per-term values from the retained model; the
    /// pins preserve the certified table-point projection for the public gate.
    fn finite_table_ground_pins(
        &self,
        model: &Model,
        grounds: &[TermId],
        table_syms: &HashMap<String, TableCertSort>,
    ) -> Option<Vec<(TermId, EvalValue)>> {
        let mut pins = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = grounds.to_vec();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    stack.extend(args.iter().copied());
                    let value = self.evaluate_term(model, term);
                    if table_syms.contains_key(sym.name()) && matches!(value, EvalValue::Unknown) {
                        return None;
                    }
                    if !matches!(value, EvalValue::Unknown) {
                        pins.push((term, value));
                    }
                }
                TermData::Not(inner) => {
                    stack.push(*inner);
                    let value = self.evaluate_term(model, term);
                    if !matches!(value, EvalValue::Unknown) {
                        pins.push((term, value));
                    }
                }
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                    let value = self.evaluate_term(model, term);
                    if !matches!(value, EvalValue::Unknown) {
                        pins.push((term, value));
                    }
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(..) | TermData::Exists(..) => return None,
                TermData::Const(_) => {}
                TermData::Var(_, _) => {
                    let value = self.evaluate_term(model, term);
                    if !matches!(value, EvalValue::Unknown) {
                        pins.push((term, value));
                    }
                }
                _ => return None,
            }
        }
        pins.sort_by_key(|(term, _)| term.0);
        Some(pins)
    }

    // =====================================================================
    // (#p2-default-row) c2: n-ary bare-tuple default-row SAT certificate.
    // =====================================================================

    /// CERTIFIED SAT for quantified UFLIA snapshots in the conservative
    /// "n-ary bare-tuple + default row" class — the multi-binder
    /// generalization of CAP-1 for foralls like `∀x,y:Int. p(x,y)`.
    /// Directly adjacent authored towers (`∀x. ∀y. B`) are treated as
    /// the same binder vector, without rewriting the certificate roots: this
    /// lets the checked package remain bound to the exact publication window.
    ///
    /// # Certificate class (everything else returns `None` — fail closed)
    ///
    /// WHOLE-SNAPSHOT requirement: every assertion must be either
    /// quantifier-free ("ground original") or a ROOT `forall` in class:
    /// - every binder is `Int`-sorted (≥ 1 binder);
    /// - every binder-DEPENDENT subterm of the body is either (a) an
    ///   application of an uninterpreted `Bool`/`Int`-codomain UF to a tuple
    ///   of DISTINCT BARE binder variables ("table app"), or (b) an
    ///   interpreted node from the CAP-1 whitelist (`and or not => xor ite =
    ///   distinct < <= > >= + - * to_real`; `/ div mod abs` reject) whose
    ///   binder-dependence flows only through (a)/(b) children. A binder
    ///   occurring anywhere else (bare in an atom like `(= x 0)`, shifted
    ///   `f(x+1)`, mixed `p(x, c)`) rejects. Binder-FREE subterms are
    ///   unconstrained (they stay symbolic in the residual sub-solve, which
    ///   only strengthens it).
    ///
    /// # The interpretation `M'` and the machine-checked totality argument
    ///
    /// For each table symbol `f`: collect EVERY fully-ground application in
    /// the snapshot into `table_f = {eval_M(args⃗) → eval_M(f(args⃗))}` and set
    /// `M'(f) = λc⃗. if c⃗ ∈ dom(table_f) then table_f(c⃗) else d_f` for an
    /// enumerated constant default `d_f`; all other symbols keep `M`.
    ///
    /// 1. GROUND ORIGINALS: re-evaluated under `M` to a definite
    ///    `Bool(true)`; `M'` agrees with `M` at every ground application
    ///    point (they are exactly the table rows), so `M' ⊨` grounds.
    /// 2. FORALLS — ONE symbolic residual sub-solve covering ALL of `Z^n`
    ///    (review-mandated: the pointwise+default split of an earlier draft
    ///    missed MIXED tuples where some coordinates hit table keys and
    ///    others fall in the default region): substitute each binder with a
    ///    fresh `Int` constant `k_i`, replace every table app by its FULL
    ///    `ite`-over-table + default expansion at those constants, and
    ///    require an independent ground refutation of `¬B_expanded`
    ///    ([`Self::checked_ground_solve`]). UNSAT is exactly
    ///    "`B_expanded` valid for every k⃗ ∈ Z^n and EVERY interpretation of
    ///    the remaining (binder-free) symbols — in particular `M'`". At any
    ///    point c⃗ the expansion evaluates to `M'(f)(c⃗)` by construction
    ///    (table row where c⃗ matches, `d_f` otherwise — including mixed
    ///    regions), so `M' ⊨ ∀x⃗.B`.
    /// 3. Steps 1–2 share one `M'` (one default vector), so `M' ⊨ snapshot`.
    ///
    /// Grant-only: never produces or influences an UNSAT verdict. On success
    /// the certified tables + defaults are INSTALLED into the model's EUF
    /// function tables so the printed `(define-fun ...)` else-branch is the
    /// certified default (the printer's else is the last table row).
    pub(in crate::executor) fn try_default_row_sat_certificate(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<()> {
        use num_bigint::BigInt;

        if self.external_stop_reason().is_some() {
            return None;
        }
        let model = self.last_model.clone()?;

        // ---- 1. Whole-snapshot partition.
        let mut foralls: Vec<TermId> = Vec::new();
        let mut grounds: Vec<TermId> = Vec::new();
        for &a in snapshot {
            match self.ctx.terms.get(a) {
                TermData::Forall(..) => foralls.push(a),
                _ if contains_quantifier(&self.ctx.terms, a) => return None,
                _ => grounds.push(a),
            }
        }
        if foralls.is_empty() {
            return None;
        }

        // ---- 2. Class scan of every forall.
        struct RowForallInfo {
            binder_names: Vec<String>,
            body: TermId,
            xdep: HashSet<TermId>,
        }
        // table symbol name -> (arity, codomain)
        let mut table_syms: HashMap<String, (usize, TableCertSort)> = HashMap::default();
        let mut infos: Vec<RowForallInfo> = Vec::with_capacity(foralls.len());
        for &q in &foralls {
            let (binder_names, body) = self.default_row_forall_tower(q)?;
            if contains_quantifier(&self.ctx.terms, body) {
                return None;
            }
            let name_set: HashSet<String> = binder_names.iter().cloned().collect();
            if name_set.len() != binder_names.len() {
                return None;
            }
            let xdep = self.default_row_xdep_nodes(body, &name_set);
            self.default_row_scan_body(body, &name_set, &xdep, &mut table_syms)?;
            infos.push(RowForallInfo {
                binder_names,
                body,
                xdep,
            });
        }
        if table_syms.is_empty() {
            return None;
        }

        let mut checked_names: Vec<&String> = table_syms.keys().collect();
        checked_names.sort_unstable();
        let requests: Vec<ay_frontend::ProjectionBindingRequest> = checked_names
            .into_iter()
            .map(|name| {
                let &(arity, codomain) = table_syms.get(name)?;
                let result_sort = match codomain {
                    TableCertSort::Bool => Sort::Bool,
                    TableCertSort::Int => Sort::Int,
                    TableCertSort::Real => Sort::Real,
                };
                Some(ay_frontend::ProjectionBindingRequest {
                    symbol: Symbol::named(name),
                    parameter_sorts: vec![Sort::Int; arity],
                    result_sort,
                })
            })
            .collect::<Option<_>>()?;
        let checked_table_bindings =
            self.check_table_declaration_occurrences(snapshot, &requests)?;

        // ---- 3. Independent re-verification of the ground originals.
        for &g in &grounds {
            if !matches!(self.evaluate_term(&model, g), EvalValue::Bool(true)) {
                return None;
            }
        }

        // ---- 4. Build the tables from EVERY fully-ground application of a
        //         table symbol anywhere in the snapshot.
        let tables = self.default_row_collect_tables(&model, snapshot, &foralls, &table_syms)?;

        // ---- 5. Default-vector candidates.
        let mut sym_names: Vec<String> = table_syms.keys().cloned().collect();
        sym_names.sort_unstable();
        let mut body_consts: Vec<BigInt> = Vec::new();
        for info in &infos {
            self.finite_table_collect_int_consts(info.body, &mut body_consts);
        }
        body_consts.sort();
        body_consts.dedup();
        body_consts.truncate(3);
        let mut candidates_per_sym: Vec<Vec<TableCertVal>> = Vec::with_capacity(sym_names.len());
        for name in &sym_names {
            let (_, codomain) = *table_syms.get(name)?;
            let mut cands: Vec<TableCertVal> = Vec::new();
            match codomain {
                TableCertSort::Bool => {
                    cands.push(TableCertVal::Bool(true));
                    cands.push(TableCertVal::Bool(false));
                }
                TableCertSort::Int => {
                    let mut ints: Vec<BigInt> =
                        vec![BigInt::ZERO, BigInt::from(1), BigInt::from(-1)];
                    if let Some(rows) = tables.get(name) {
                        let mut vals: Vec<BigInt> = rows
                            .iter()
                            .filter_map(|(_, v)| match v {
                                TableCertVal::Int(i) => Some(i.clone()),
                                _ => None,
                            })
                            .collect();
                        vals.sort();
                        vals.dedup();
                        ints.extend(vals.into_iter().take(2));
                    }
                    ints.extend(body_consts.iter().cloned());
                    let mut seen: HashSet<BigInt> = HashSet::default();
                    for v in ints {
                        if cands.len() >= MAX_TABLE_CERT_DEFAULTS_PER_SYM {
                            break;
                        }
                        if seen.insert(v.clone()) {
                            cands.push(TableCertVal::Int(v));
                        }
                    }
                }
                // Real codomains are out of class (format/eval risk not worth
                // the parity; fail closed).
                TableCertSort::Real => return None,
            }
            candidates_per_sym.push(cands);
        }

        // ---- 6. Fresh binder constants (one vector per forall, reused
        //         across default combos).
        let mut binder_ks: Vec<HashMap<String, TermId>> = Vec::with_capacity(infos.len());
        for info in &infos {
            let mut map: HashMap<String, TermId> = HashMap::default();
            for name in &info.binder_names {
                let k = self.ctx.terms.mk_fresh_var("ay_c2_k", Sort::Int);
                map.insert(name.clone(), k);
            }
            binder_ks.push(map);
        }

        // ---- 7. Mixed-radix default-vector enumeration; one symbolic
        //         residual sub-solve per (forall, combo).
        let mut solver_calls = 0usize;
        let mut failed_residuals: HashSet<TermId> = HashSet::default();
        let mut combo_idx: Vec<usize> = vec![0; sym_names.len()];
        let mut combo_count = 0usize;
        loop {
            combo_count += 1;
            if combo_count > MAX_TABLE_CERT_DEFAULT_COMBOS {
                return None;
            }
            let defaults: HashMap<String, TableCertVal> = sym_names
                .iter()
                .enumerate()
                .map(|(si, n)| (n.clone(), candidates_per_sym[si][combo_idx[si]].clone()))
                .collect();

            let mut all_pass = true;
            for (fi, info) in infos.iter().enumerate() {
                let expanded = self.default_row_expand(
                    info.body,
                    &binder_ks[fi],
                    &info.xdep,
                    &table_syms,
                    &tables,
                    &defaults,
                )?;
                let formula = self.ctx.terms.mk_not(expanded);
                if failed_residuals.contains(&formula) {
                    all_pass = false;
                    break;
                }
                if solver_calls >= MAX_TABLE_CERT_SOLVER_CALLS
                    || self.external_stop_reason().is_some()
                {
                    return None;
                }
                solver_calls += 1;
                let obligation = vec![formula];
                if !self
                    .checked_ground_solve(obligation.clone(), fallback_category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    failed_residuals.insert(formula);
                    all_pass = false;
                    break;
                }
            }
            if all_pass {
                self.install_default_row_model(
                    snapshot,
                    model,
                    &table_syms,
                    &tables,
                    &defaults,
                    checked_table_bindings,
                )?;
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!(
                        "CERT/default-row: certified SAT ({} foralls, {} table syms)",
                        infos.len(),
                        sym_names.len()
                    );
                }
                return Some(());
            }

            let mut carry = true;
            for i in (0..combo_idx.len()).rev() {
                if carry {
                    combo_idx[i] += 1;
                    if combo_idx[i] < candidates_per_sym[i].len() {
                        carry = false;
                    } else {
                        combo_idx[i] = 0;
                    }
                }
            }
            if carry {
                return None;
            }
        }
    }

    /// Peel one directly-adjacent authored `forall` tower into the binder
    /// vector and quantifier-free body used by the default-row theorem.
    ///
    /// This is a read-only logical view, not a term rewrite: the publication
    /// package stays scoped to `root` and therefore to the exact authored root
    /// vector. Every level must remain in the certificate's existing Int-only,
    /// MBQI-eligible class. Duplicate names fail closed because the certificate
    /// evaluator keys bound variables by name and must not conflate shadowed
    /// binders.
    fn default_row_forall_tower(&self, root: TermId) -> Option<(Vec<String>, TermId)> {
        let mut binders = Vec::new();
        let mut seen = HashSet::default();
        let mut current = root;
        loop {
            if self.ctx.terms.is_no_mbqi(current) {
                return None;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(current) else {
                return None;
            };
            if vars.is_empty() {
                return None;
            }
            for (name, sort) in vars {
                if *sort != Sort::Int || !seen.insert(name.clone()) {
                    return None;
                }
                binders.push(name.clone());
            }
            match self.ctx.terms.get(*body) {
                TermData::Forall(..) => current = *body,
                _ => return Some((binders, *body)),
            }
        }
    }

    /// Nodes of `body` (as a DAG) that mention ANY of the binder names.
    fn default_row_xdep_nodes(
        &self,
        body: TermId,
        binder_names: &HashSet<String>,
    ) -> HashSet<TermId> {
        let mut order: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<(TermId, bool)> = vec![(body, false)];
        while let Some((t, processed)) = stack.pop() {
            if processed {
                order.push(t);
                continue;
            }
            if !visited.insert(t) {
                continue;
            }
            stack.push((t, true));
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => {
                    for &a in args {
                        stack.push((a, false));
                    }
                }
                TermData::Not(i) => stack.push((*i, false)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, false));
                    stack.push((*a, false));
                    stack.push((*b, false));
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push((*v, false));
                    }
                    stack.push((*b, false));
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push((*b, false)),
                _ => {}
            }
        }
        let mut xdep: HashSet<TermId> = HashSet::default();
        for &t in &order {
            let dep = match self.ctx.terms.get(t) {
                TermData::Var(name, _) => binder_names.contains(name),
                TermData::App(_, args) => args.iter().any(|a| xdep.contains(a)),
                TermData::Not(i) => xdep.contains(i),
                TermData::Ite(c, a, b) => xdep.contains(c) || xdep.contains(a) || xdep.contains(b),
                TermData::Let(bindings, b) => {
                    xdep.contains(b) || bindings.iter().any(|(_, v)| xdep.contains(v))
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => xdep.contains(b),
                _ => false,
            };
            if dep {
                xdep.insert(t);
            }
        }
        xdep
    }

    /// Class scan for one default-row forall body (see
    /// [`Self::try_default_row_sat_certificate`] for the class definition).
    fn default_row_scan_body(
        &self,
        body: TermId,
        binder_names: &HashSet<String>,
        xdep: &HashSet<TermId>,
        table_syms: &mut HashMap<String, (usize, TableCertSort)>,
    ) -> Option<()> {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if !xdep.contains(&t) {
                // Binder-free: stays symbolic in the residual sub-solve —
                // no structural restriction needed.
                continue;
            }
            match self.ctx.terms.get(t) {
                // A bare binder OUTSIDE a table application (`(= x 0)`,
                // `(+ x 1)`, ...) is out of class — binder dependence must
                // flow only through table apps.
                TermData::Var(_, _) => return None,
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if matches!(name, "/" | "div" | "mod" | "abs") {
                        return None;
                    }
                    if is_finite_table_interpreted_symbol(name) {
                        stack.extend(args.iter().copied());
                        continue;
                    }
                    if is_pure_arith_bool_symbol(name) || is_interpreted_bv_symbol(name) {
                        return None;
                    }
                    if !is_mbqi_completable_uf_symbol(name)
                        || self.symbol_is_datatype_selector_or_constructor(name)
                    {
                        return None;
                    }
                    // Uninterpreted, binder-dependent: must be a table app —
                    // every arg a DISTINCT bare binder variable.
                    let mut seen_names: HashSet<&str> = HashSet::default();
                    for &a in args {
                        match self.ctx.terms.get(a) {
                            TermData::Var(n, _)
                                if binder_names.contains(n) && seen_names.insert(n.as_str()) => {}
                            _ => return None,
                        }
                    }
                    let codomain = match self.ctx.terms.sort(t) {
                        Sort::Bool => TableCertSort::Bool,
                        Sort::Int => TableCertSort::Int,
                        _ => return None,
                    };
                    match table_syms.get(name) {
                        Some(&(arity, cs)) if arity != args.len() || cs != codomain => {
                            return None;
                        }
                        Some(_) => {}
                        None => {
                            table_syms.insert(name.to_string(), (args.len(), codomain));
                        }
                    }
                    // Args are bare binders — nothing further to scan below.
                }
                // Let / nested quantifiers / anything else binder-dependent:
                // out of class.
                _ => return None,
            }
        }
        Some(())
    }

    /// Collect table rows: every FULLY-GROUND application of a table symbol
    /// anywhere in the snapshot, keyed by exact integer argument values.
    /// `None` on arity mismatch, unevaluable points, value conflicts, or
    /// overflow. An application whose args are the enclosing forall's bare
    /// binders is the certified shape (skipped); any OTHER binder-dependent
    /// occurrence fails closed.
    fn default_row_collect_tables(
        &self,
        model: &Model,
        snapshot: &[TermId],
        foralls: &[TermId],
        table_syms: &HashMap<String, (usize, TableCertSort)>,
    ) -> Option<HashMap<String, Vec<(Vec<num_bigint::BigInt>, TableCertVal)>>> {
        use num_bigint::BigInt;
        let forall_set: HashSet<TermId> = foralls.iter().copied().collect();
        let mut tables: HashMap<String, Vec<(Vec<BigInt>, TableCertVal)>> = HashMap::default();
        for name in table_syms.keys() {
            tables.insert(name.clone(), Vec::new());
        }
        let mut total_points = 0usize;
        for &root in snapshot {
            let (binders, walk_root): (HashSet<String>, TermId) = if forall_set.contains(&root) {
                let (names, body) = self.default_row_forall_tower(root)?;
                let binders: HashSet<String> = names.into_iter().collect();
                if binders.is_empty() {
                    return None;
                }
                (binders, body)
            } else {
                (HashSet::default(), root)
            };
            let mut visited: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = vec![walk_root];
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(sym, args) => {
                        stack.extend(args.iter().copied());
                        let name = sym.name();
                        let Some(&(arity, codomain)) = table_syms.get(name) else {
                            continue;
                        };
                        if args.len() != arity {
                            return None;
                        }
                        let is_binder_app = args.iter().all(|&a| {
                            matches!(self.ctx.terms.get(a),
                                     TermData::Var(n, _) if binders.contains(n))
                        });
                        if is_binder_app && !binders.is_empty() {
                            continue; // the certified shape, not a table point
                        }
                        // Any partial binder mention is out of class.
                        if args
                            .iter()
                            .any(|&a| binders.iter().any(|b| self.finite_table_mentions_var(a, b)))
                        {
                            return None;
                        }
                        // Fully-ground application: a value-keyed table row.
                        let mut key: Vec<BigInt> = Vec::with_capacity(args.len());
                        for &a in args {
                            match self.evaluate_term(model, a) {
                                EvalValue::Rational(r) if r.is_integer() => {
                                    key.push(r.numer().clone());
                                }
                                _ => return None,
                            }
                        }
                        let val = match (codomain, self.evaluate_term(model, t)) {
                            (TableCertSort::Bool, EvalValue::Bool(b)) => TableCertVal::Bool(b),
                            (TableCertSort::Int, EvalValue::Rational(r)) if r.is_integer() => {
                                TableCertVal::Int(r.numer().clone())
                            }
                            _ => return None,
                        };
                        let rows = tables.get_mut(name)?;
                        match rows.iter().find(|(k, _)| *k == key) {
                            Some((_, existing)) if *existing != val => return None,
                            Some(_) => {}
                            None => {
                                total_points += 1;
                                if total_points > MAX_TABLE_CERT_POINTS_TOTAL {
                                    return None;
                                }
                                rows.push((key, val));
                            }
                        }
                    }
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    TermData::Let(bindings, b) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*b);
                    }
                    TermData::Forall(..) | TermData::Exists(..) => return None,
                    _ => {}
                }
            }
        }
        Some(tables)
    }

    /// Rebuild `t` with every binder variable replaced by its fresh constant
    /// and every table application replaced by its FULL
    /// `ite`-over-table + default expansion. Binder-free subterms are left
    /// untouched (symbolic in the sub-solve).
    fn default_row_expand(
        &mut self,
        t: TermId,
        binder_ks: &HashMap<String, TermId>,
        xdep: &HashSet<TermId>,
        table_syms: &HashMap<String, (usize, TableCertSort)>,
        tables: &HashMap<String, Vec<(Vec<num_bigint::BigInt>, TableCertVal)>>,
        defaults: &HashMap<String, TableCertVal>,
    ) -> Option<TermId> {
        if !xdep.contains(&t) {
            return Some(t);
        }
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            match self.ctx.terms.get(t).clone() {
                TermData::Var(name, _) => binder_ks.get(&name).copied(),
                TermData::Not(i) => {
                    let ni =
                        self.default_row_expand(i, binder_ks, xdep, table_syms, tables, defaults)?;
                    Some(self.ctx.terms.mk_not(ni))
                }
                TermData::Ite(c, a, b) => {
                    let nc =
                        self.default_row_expand(c, binder_ks, xdep, table_syms, tables, defaults)?;
                    let na =
                        self.default_row_expand(a, binder_ks, xdep, table_syms, tables, defaults)?;
                    let nb =
                        self.default_row_expand(b, binder_ks, xdep, table_syms, tables, defaults)?;
                    Some(self.ctx.terms.mk_ite(nc, na, nb))
                }
                TermData::App(sym, args) => {
                    let name = sym.name().to_string();
                    if table_syms.contains_key(&name) {
                        // Table app over bare binders: expand to the full
                        // ite(table) + default chain at the fresh constants.
                        let mut ks: Vec<TermId> = Vec::with_capacity(args.len());
                        for &a in &args {
                            let TermData::Var(n, _) = self.ctx.terms.get(a) else {
                                return None;
                            };
                            ks.push(*binder_ks.get(n)?);
                        }
                        let default = defaults.get(&name)?;
                        let mut chain = self.table_cert_val_literal(default);
                        let rows = tables.get(&name)?;
                        for (key, val) in rows.iter().rev() {
                            if key.len() != ks.len() {
                                return None;
                            }
                            let mut conds: Vec<TermId> = Vec::with_capacity(ks.len());
                            for (j, kv) in key.iter().enumerate() {
                                let lit = self.ctx.terms.mk_int(kv.clone());
                                conds.push(self.ctx.terms.mk_eq(ks[j], lit));
                            }
                            let cond = self.ctx.terms.mk_and(conds);
                            let val_lit = self.table_cert_val_literal(val);
                            chain = self.ctx.terms.mk_ite(cond, val_lit, chain);
                        }
                        Some(chain)
                    } else {
                        let mut new_args: Vec<TermId> = Vec::with_capacity(args.len());
                        for &a in &args {
                            new_args.push(self.default_row_expand(
                                a, binder_ks, xdep, table_syms, tables, defaults,
                            )?);
                        }
                        let sort = self.ctx.terms.sort(t).clone();
                        Some(self.ctx.terms.mk_app(sym, new_args, sort))
                    }
                }
                _ => None,
            }
        })
    }

    fn table_cert_val_literal(&mut self, v: &TableCertVal) -> TermId {
        match v {
            TableCertVal::Bool(b) => self.ctx.terms.mk_bool(*b),
            TableCertVal::Int(i) => self.ctx.terms.mk_int(i.clone()),
            TableCertVal::Rat(r) => self.ctx.terms.mk_rational(r.clone()),
        }
    }

    /// Materialize the exact finite-table interpretation certified by
    /// [`Self::try_finite_table_sat_certificate`] into `model`.
    ///
    /// The certificate proves satisfiability of `M'`, not necessarily of the
    /// ground solver's incoming candidate `M`. Publishing `M` after that proof
    /// can therefore return a correct `sat` verdict with a false model. Build
    /// every replacement table first and install them into a private clone, so
    /// any malformed/missing row fails closed without partially mutating the
    /// caller's model.
    fn install_finite_table_model(
        &self,
        model: &mut Model,
        table_syms: &HashMap<String, TableCertSort>,
        table_arg_sorts: &HashMap<String, Vec<Sort>>,
        tables: &HashMap<String, HashMap<TableCertKey, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        checked_bindings: &[ay_frontend::CheckedProjectionBinding],
    ) -> Option<()> {
        fn semantic_value(v: &TableCertVal) -> EvalValue {
            match v {
                TableCertVal::Bool(b) => EvalValue::Bool(*b),
                TableCertVal::Int(i) => {
                    EvalValue::Rational(num_rational::BigRational::from_integer(i.clone()))
                }
                TableCertVal::Rat(r) => EvalValue::Rational(r.clone()),
            }
        }
        fn result_sort(kind: TableCertSort) -> Sort {
            match kind {
                TableCertSort::Bool => Sort::Bool,
                TableCertSort::Int => Sort::Int,
                TableCertSort::Real => Sort::Real,
            }
        }
        if checked_bindings.len() != table_syms.len()
            || checked_bindings.len() != table_arg_sorts.len()
            || checked_bindings.len() != tables.len()
            || checked_bindings.len() != defaults.len()
            || checked_bindings
                .iter()
                .any(|binding| !self.ctx.projection_binding_still_current(binding))
        {
            return None;
        }
        type Replacement = (
            String,
            Vec<Sort>,
            Sort,
            Vec<(Vec<EvalValue>, EvalValue)>,
            EvalValue,
        );
        let mut replacements: Vec<Replacement> = Vec::with_capacity(checked_bindings.len());
        for binding in checked_bindings {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            let arg_sorts = table_arg_sorts.get(name)?.clone();
            let arity = arg_sorts.len();
            if arity == 0 || binding.parameter_sorts() != arg_sorts {
                return None;
            }
            let codomain = result_sort(*table_syms.get(name)?);
            if binding.result_sort() != &codomain {
                return None;
            }
            let rows = tables.get(name)?;
            let default = defaults.get(name)?;
            let mut sorted_rows: Vec<(&TableCertKey, &TableCertVal)> = rows.iter().collect();
            sorted_rows.sort_by(|a, b| a.0.cmp(b.0));

            let mut semantic_rows: Vec<(Vec<EvalValue>, EvalValue)> =
                Vec::with_capacity(rows.len());
            for ((prefix, point), value) in sorted_rows {
                if prefix.len().checked_add(1)? != arity {
                    return None;
                }
                let mut semantic_args: Vec<EvalValue> =
                    prefix.iter().cloned().map(EvalValue::Rational).collect();
                semantic_args.push(EvalValue::Rational(point.clone()));
                semantic_rows.push((semantic_args, semantic_value(value)));
            }

            replacements.push((
                name.clone(),
                arg_sorts,
                codomain,
                semantic_rows,
                semantic_value(default),
            ));
        }

        let mut completed = model.clone();
        for (name, arg_sorts, codomain, rows, default) in replacements {
            completed.install_certified_total_uf(name, arg_sorts, codomain, rows, default)?;
        }
        *model = completed;
        Some(())
    }

    /// Install the certified table + default interpretation into the model's
    /// EUF function tables so both the printed `(define-fun ...)` (whose else
    /// branch is the LAST row's value) and `(get-value ...)` reads agree with
    /// the certified `M'`. Real rows come first (a scan takes the first
    /// match); the synthetic final row carries the default as the else value
    /// — its argument tuple is never printed as a condition.
    fn install_default_row_model(
        &mut self,
        roots: &[TermId],
        mut completed: Model,
        table_syms: &HashMap<String, (usize, TableCertSort)>,
        tables: &HashMap<String, Vec<(Vec<num_bigint::BigInt>, TableCertVal)>>,
        defaults: &HashMap<String, TableCertVal>,
        checked_bindings: Vec<ay_frontend::CheckedProjectionBinding>,
    ) -> Option<()> {
        fn semantic_value(v: &TableCertVal) -> EvalValue {
            match v {
                TableCertVal::Bool(b) => EvalValue::Bool(*b),
                TableCertVal::Int(i) => {
                    EvalValue::Rational(num_rational::BigRational::from_integer(i.clone()))
                }
                TableCertVal::Rat(r) => EvalValue::Rational(r.clone()),
            }
        }
        if checked_bindings.len() != table_syms.len()
            || checked_bindings.len() != tables.len()
            || checked_bindings.len() != defaults.len()
            || checked_bindings
                .iter()
                .any(|binding| !self.ctx.projection_binding_still_current(binding))
        {
            return None;
        }
        for binding in &checked_bindings {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            let &(arity, codomain) = table_syms.get(name)?;
            if arity == 0
                || binding.parameter_sorts().len() != arity
                || binding
                    .parameter_sorts()
                    .iter()
                    .any(|sort| sort != &Sort::Int)
            {
                return None;
            }
            let rows = tables.get(name)?;
            let default = defaults.get(name)?;
            let mut sorted_rows: Vec<&(Vec<num_bigint::BigInt>, TableCertVal)> =
                rows.iter().collect();
            sorted_rows.sort_by(|a, b| a.0.cmp(&b.0));
            let semantic_rows: Vec<(Vec<EvalValue>, EvalValue)> = sorted_rows
                .iter()
                .map(|(key, value)| {
                    (
                        key.iter()
                            .cloned()
                            .map(num_rational::BigRational::from_integer)
                            .map(EvalValue::Rational)
                            .collect(),
                        semantic_value(value),
                    )
                })
                .collect();
            let result_sort = match codomain {
                TableCertSort::Bool => Sort::Bool,
                TableCertSort::Int => Sort::Int,
                TableCertSort::Real => Sort::Real,
            };
            if binding.result_sort() != &result_sort {
                return None;
            }
            completed.install_certified_total_uf(
                name.clone(),
                vec![Sort::Int; arity],
                result_sort,
                semantic_rows,
                semantic_value(default),
            )?;
        }
        // Nested residual probes may have left a different certificate model
        // in `last_model`. The default-row theorem publishes only the total
        // tables constructed above; never inherit another model's ground
        // projection merely because `completed` started as its clone.
        completed.install_quantified_certificate_pins(
            &self.ctx.terms,
            std::iter::empty::<(TermId, EvalValue)>(),
        )?;
        // Match the finite-table sibling's linear publication contract. Later
        // mapper probes can overwrite `last_model`, so retain the exact
        // default-row interpretation for atomic installation by the public SAT
        // funnel. This certificate has no separate ground-term pin sidecar.
        self.finite_table_cert_witness_state =
            Some(FiniteTableWitnessState::pending_for_current_query(
                self,
                roots,
                checked_bindings,
                completed,
            )?);
        Some(())
    }

    /// Materialize the exact F4 datatype-table completion proved by the DT SAT
    /// certificate. Every certificate e-class key must have a checked,
    /// same-sorted representative that resolves to one concrete constructor
    /// value. That concrete value becomes both the typed evaluation key and the
    /// constructor spelling published by the model; an abstract e-graph token
    /// itself is never model data.
    fn install_dt_f4_model(
        &mut self,
        table_syms: &HashMap<String, TableCertSort>,
        tables: &HashMap<String, HashMap<String, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        table_key_reps: &HashMap<(String, String), TermId>,
        checked_bindings: &[ay_frontend::CheckedProjectionBinding],
        grounds: &[TermId],
    ) -> Option<()> {
        fn semantic_value(value: &TableCertVal) -> EvalValue {
            match value {
                TableCertVal::Bool(value) => EvalValue::Bool(*value),
                TableCertVal::Int(value) => {
                    EvalValue::Rational(num_rational::BigRational::from_integer(value.clone()))
                }
                TableCertVal::Rat(value) => EvalValue::Rational(value.clone()),
            }
        }
        fn result_sort(kind: TableCertSort) -> Sort {
            match kind {
                TableCertSort::Bool => Sort::Bool,
                TableCertSort::Int => Sort::Int,
                TableCertSort::Real => Sort::Real,
            }
        }
        let trace_decline = |reason: &str| {
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace dt-cert-model-install-decline reason={reason}");
            }
        };

        if checked_bindings.len() != table_syms.len()
            || checked_bindings.len() != tables.len()
            || checked_bindings.len() != defaults.len()
            || checked_bindings
                .iter()
                .any(|binding| !self.ctx.projection_binding_still_current(binding))
        {
            trace_decline("authority-cardinality-or-epoch");
            return None;
        }
        let Some(source_model) = self.last_model.as_ref() else {
            trace_decline("missing-source-model");
            return None;
        };
        type Replacement = (
            String,
            Vec<Sort>,
            Sort,
            Vec<(Vec<EvalValue>, EvalValue)>,
            Vec<Vec<String>>,
            EvalValue,
        );
        let mut replacements: Vec<Replacement> = Vec::with_capacity(checked_bindings.len());
        for binding in checked_bindings {
            let Symbol::Named(name) = binding.symbol() else {
                return None;
            };
            if binding.parameter_sorts().len() != 1
                || self
                    .dt_cert_sort_name(&binding.parameter_sorts()[0])
                    .is_none()
            {
                return None;
            }
            let codomain = result_sort(*table_syms.get(name)?);
            if binding.result_sort() != &codomain {
                return None;
            }
            let table = tables.get(name)?;
            let mut sorted_rows: Vec<(&String, &TableCertVal)> = table.iter().collect();
            sorted_rows.sort_by(|a, b| a.0.cmp(b.0));
            let mut rows = Vec::with_capacity(sorted_rows.len());
            let mut rendered_arguments = Vec::with_capacity(sorted_rows.len());
            for (key, value) in sorted_rows {
                let Some(&representative) = table_key_reps.get(&(name.clone(), key.clone())) else {
                    trace_decline("missing-row-representative");
                    return None;
                };
                if self.ctx.terms.sort(representative) != &binding.parameter_sorts()[0]
                    || source_model
                        .dt_pins
                        .get(&representative)
                        .is_some_and(|pin| pin != &EvalValue::Element(key.clone()))
                {
                    trace_decline("row-representative-pin-mismatch");
                    return None;
                }
                // Bind the printed exception key to the same single-source DT
                // surface value used for constants and fresh get-value terms.
                // Combined lanes without an e-graph export use the exact gate
                // reconstruction that certified this representative.
                let Some(rendered) = self.certified_dt_surface_value(source_model, representative)
                else {
                    trace_decline("row-surface-unavailable");
                    return None;
                };
                // The certificate's table key may be an internal EUF e-class
                // token (`@D!n`). Once its checked representative has been
                // resolved into the concrete M' surface value, store that
                // concrete value as the typed identity too. Abstract tokens
                // are deliberately inadmissible model data, and keeping one
                // here would make evaluation and output name the same point
                // in two incompatible vocabularies.
                rows.push((
                    vec![EvalValue::Element(rendered.clone())],
                    semantic_value(value),
                ));
                rendered_arguments.push(vec![rendered]);
            }
            replacements.push((
                name.clone(),
                binding.parameter_sorts().to_vec(),
                codomain,
                rows,
                rendered_arguments,
                semantic_value(defaults.get(name)?),
            ));
        }

        let mut completed = source_model.clone();
        for (name, arg_sorts, codomain, rows, rendered_arguments, default) in replacements {
            if completed
                .install_certified_total_dt_uf(
                    name,
                    arg_sorts,
                    codomain,
                    rows,
                    rendered_arguments,
                    default,
                )
                .is_none()
            {
                trace_decline("typed-table-install-rejected");
                return None;
            }
        }
        // The installed typed interpretation must preserve every ground
        // assertion already discharged by the certificate.  This catches any
        // mismatch between DT row identity and ordinary model evaluation before
        // the completed model can become publication authority.
        for &ground in grounds {
            let value = self.evaluate_term(&completed, ground);
            if !matches!(value, EvalValue::Bool(true)) {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!(
                        "c phase-trace dt-cert-model-install-decline reason=ground-recheck term={} value={value:?} expr={}",
                        ground.0,
                        self.format_term(ground)
                    );
                }
                return None;
            }
        }
        self.last_model = Some(completed);
        Some(())
    }

    /// Check every certified forall under one concrete default vector.
    /// Returns `Some(true)` when all pointwise + residual checks pass,
    /// `Some(false)` when this default vector fails (caller tries the next),
    /// and `None` on a hard budget/deadline stop (caller aborts entirely).
    #[allow(clippy::too_many_arguments)]
    fn finite_table_check_all(
        &mut self,
        model: &Model,
        infos: &[(&str, &Sort, TermId, &HashSet<TermId>, &[String])],
        points_per_forall: &[Vec<num_rational::BigRational>],
        tables: &HashMap<String, HashMap<TableCertKey, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        category: LogicCategory,
        solver_calls: &mut usize,
        failed_residuals: &mut HashSet<TermId>,
    ) -> Option<bool> {
        for (fi, &(var_name, var_sort, body, xdep, _body_syms)) in infos.iter().enumerate() {
            // Pointwise leg: exact evaluation at every table point.
            for c in &points_per_forall[fi] {
                match self
                    .finite_table_eval(model, body, var_name, var_sort, c, xdep, tables, defaults)
                {
                    Some(TableCertVal::Bool(true)) => {}
                    _ => return Some(false),
                }
            }
            // Residual leg.
            let mut memo: HashMap<TermId, TermId> = HashMap::default();
            let residual = self.finite_table_residual(body, var_name, xdep, defaults, &mut memo)?;
            if !self.finite_table_mentions_var(residual, var_name) {
                match self.evaluate_term(model, residual) {
                    EvalValue::Bool(true) => {}
                    _ => return Some(false),
                }
            } else {
                if failed_residuals.contains(&residual) {
                    return Some(false);
                }
                if *solver_calls >= MAX_TABLE_CERT_SOLVER_CALLS
                    || self.external_stop_reason().is_some()
                {
                    return None;
                }
                *solver_calls += 1;
                // The fresh constant carries the BINDER's sort, so the
                // refutation quantifies over exactly the binder's domain
                // (see the residual-leg note in the certificate doc).
                let fresh = self
                    .ctx
                    .terms
                    .mk_fresh_var("__ay_cap1_table_cert", var_sort.clone());
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(var_name.to_string(), fresh);
                let residual_at_k = subst_vars(&mut self.ctx.terms, residual, &subst);
                let mut conj: Vec<TermId> = vec![self.ctx.terms.mk_not(residual_at_k)];
                for p in &points_per_forall[fi] {
                    let pc = match var_sort {
                        Sort::Int => {
                            // Int-binder points are integer-valued rationals
                            // by construction; anything else fails closed.
                            if !p.is_integer() {
                                return None;
                            }
                            self.ctx.terms.mk_int(p.numer().clone())
                        }
                        Sort::Real => self.ctx.terms.mk_rational(p.clone()),
                        _ => return None,
                    };
                    let eq = self.ctx.terms.mk_eq(fresh, pc);
                    conj.push(self.ctx.terms.mk_not(eq));
                }
                let formula = self.ctx.terms.mk_and(conj);
                let obligation = vec![formula];
                if !self
                    .checked_ground_solve(obligation.clone(), category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    failed_residuals.insert(residual);
                    return Some(false);
                }
            }
        }
        Some(true)
    }

    /// Nodes of `body` (as a DAG) that contain the bound variable `var_name`.
    fn finite_table_xdep_nodes(&self, body: TermId, var_name: &str) -> HashSet<TermId> {
        // Post-order over the DAG, then one bottom-up dependency pass.
        let mut order: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<(TermId, bool)> = vec![(body, false)];
        while let Some((t, processed)) = stack.pop() {
            if processed {
                order.push(t);
                continue;
            }
            if !visited.insert(t) {
                continue;
            }
            stack.push((t, true));
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().map(|&a| (a, false))),
                TermData::Not(i) => stack.push((*i, false)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, false));
                    stack.push((*a, false));
                    stack.push((*b, false));
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push((*v, false));
                    }
                    stack.push((*b, false));
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push((*b, false)),
                _ => {}
            }
        }
        let mut dep: HashSet<TermId> = HashSet::default();
        for &t in &order {
            let d = match self.ctx.terms.get(t) {
                TermData::Var(n, _) => n == var_name,
                TermData::App(_, args) => args.iter().any(|a| dep.contains(a)),
                TermData::Not(i) => dep.contains(i),
                TermData::Ite(c, a, b) => dep.contains(c) || dep.contains(a) || dep.contains(b),
                TermData::Let(bindings, b) => {
                    dep.contains(b) || bindings.iter().any(|(_, v)| dep.contains(v))
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => dep.contains(b),
                _ => false,
            };
            if d {
                dep.insert(t);
            }
        }
        dep
    }

    /// Exact value of an x-free (ground under the certified binder) prefix or
    /// point argument under the candidate model, as an exact rational used as a
    /// table key. `Int`-sorted args must be integer-valued; `Real`-sorted args
    /// may be any rational. Every other sort, and any
    /// `EvalValue::Unknown`/`Algebraic`/non-numeric result, fails closed
    /// (`None`) — CCMC M1 value-keying is sound ONLY over exactly-known Int/Real
    /// prefixes (Seq-sorted prefixes are DEFERRED to M3 and rejected here). The
    /// SAME helper keys both [`Self::finite_table_collect`] (ground apps) and
    /// [`Self::finite_table_eval`] (forall-body apps), so a body `f(g, x)` and a
    /// ground `f(g', c)` land on the same row exactly when `g` and `g'` denote
    /// the same value in the model.
    fn finite_table_prefix_value(
        &self,
        model: &Model,
        arg: TermId,
    ) -> Option<num_rational::BigRational> {
        match (self.ctx.terms.sort(arg), self.evaluate_term(model, arg)) {
            (Sort::Int, EvalValue::Rational(r)) if r.is_integer() => Some(r),
            (Sort::Real, EvalValue::Rational(r)) => Some(r),
            _ => None,
        }
    }

    /// Positively bind every table head to an exact live free-UF declaration
    /// and verify complete occurrence/signature coverage over `roots`.
    ///
    /// Table certificate producers still use compact string-keyed maps
    /// internally. This boundary is what makes that representation safe: an
    /// interpreted, defined, overloaded, indexed, internal, stale, or
    /// signature-mismatched occurrence cannot cross into model installation.
    fn check_table_declaration_occurrences(
        &self,
        roots: &[TermId],
        requests: &[ay_frontend::ProjectionBindingRequest],
    ) -> Option<Vec<ay_frontend::CheckedProjectionBinding>> {
        const MAX_CHECKED_TABLE_TERMS: usize = 1_000_000;

        if requests.is_empty() || self.external_stop_reason().is_some() {
            return None;
        }
        let mut bindings = Vec::with_capacity(requests.len());
        for request in requests {
            let checked = self.ctx.check_projection_declaration(request).ok()?;
            if bindings
                .iter()
                .any(|existing: &ay_frontend::CheckedProjectionBinding| {
                    existing.symbol() == checked.symbol()
                })
            {
                return None;
            }
            bindings.push(checked);
        }

        let mut uses = vec![0usize; bindings.len()];
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_CHECKED_TABLE_TERMS
                || self.external_stop_reason().is_some()
                || term.index() >= self.ctx.terms.len()
            {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    if let Some((index, binding)) = bindings
                        .iter()
                        .enumerate()
                        .find(|(_, binding)| binding.symbol().name() == symbol.name())
                    {
                        if binding.symbol() != symbol
                            || args.len() != binding.parameter_sorts().len()
                            || self.ctx.terms.sort(term) != binding.result_sort()
                            || args
                                .iter()
                                .zip(binding.parameter_sorts())
                                .any(|(&arg, expected)| self.ctx.terms.sort(arg) != expected)
                        {
                            return None;
                        }
                        uses[index] = uses[index].saturating_add(1);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return None,
            }
        }
        if uses.iter().any(|&count| count == 0)
            || bindings
                .iter()
                .any(|binding| !self.ctx.projection_binding_still_current(binding))
        {
            return None;
        }
        Some(bindings)
    }

    /// Validate the class-A shape of one forall body (see
    /// [`Self::try_finite_table_sat_certificate`]) and record its table
    /// symbols. Returns `None` on ANY out-of-class construct.
    fn finite_table_scan_body(
        &self,
        body: TermId,
        var_name: &str,
        var_sort: &Sort,
        xdep: &HashSet<TermId>,
        table_syms: &mut HashMap<String, TableCertSort>,
        table_arg_sorts: &mut HashMap<String, Vec<Sort>>,
        body_syms: &mut HashSet<String>,
    ) -> Option<()> {
        use num_traits::Zero;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if !matches!(self.ctx.terms.sort(t), Sort::Bool | Sort::Int | Sort::Real) {
                return None;
            }
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => {}
                TermData::Const(_) => return None,
                // A variable named like the binder IS the binder (innermost-
                // binder shadowing, the engine's name-based substitution
                // convention; nested binders are rejected below, so no other
                // capture is possible). Any other name is a FREE constant
                // (declared const / skolem): x-free, model-pinned — admissible
                // exactly like a ground UF application.
                TermData::Var(_, _) => {}
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if name == "/" {
                        // Real division is admitted ONLY with literal NONZERO
                        // numeral divisors (left-associative chain: every arg
                        // after the first divides). That is the only case
                        // whose semantics is fully pinned — SMT-LIB leaves
                        // division by zero underspecified, and a symbolic
                        // divisor could be zero under some interpretation, so
                        // both the exact evaluator and the residual
                        // ground-solve leg would be reasoning about an
                        // unpinned function. Anything else fails closed.
                        if args.len() < 2 {
                            return None;
                        }
                        for &d in &args[1..] {
                            match self.ctx.terms.get(d) {
                                TermData::Const(Constant::Int(v)) if !v.is_zero() => {}
                                TermData::Const(Constant::Rational(w)) if !w.0.is_zero() => {}
                                _ => return None,
                            }
                        }
                        stack.extend(args.iter().copied());
                        continue;
                    }
                    if name == "*" && *var_sort == Sort::Real && xdep.contains(&t) {
                        // REAL-binder LINEARITY guard: an x-dependent product
                        // must be `literal * (single x-dependent factor)`.
                        // Anything else (x*x, f(x)*f(x), g(c)*x, ...) would
                        // push a NONLINEAR real formula into the residual
                        // ground solve; the certificate stays inside the
                        // linear fragment and fails closed instead. (Int
                        // binders keep the historical behavior: their
                        // residual probes may be nonlinear-integer, which the
                        // ground lane already answers fail-closed.)
                        let mut xdep_args = 0usize;
                        for &a in args {
                            if xdep.contains(&a) {
                                xdep_args += 1;
                            } else {
                                match self.ctx.terms.get(a) {
                                    TermData::Const(Constant::Int(_) | Constant::Rational(_)) => {}
                                    _ => return None,
                                }
                            }
                        }
                        if xdep_args != 1 {
                            return None;
                        }
                        stack.extend(args.iter().copied());
                        continue;
                    }
                    if is_finite_table_interpreted_symbol(name) {
                        stack.extend(args.iter().copied());
                        continue;
                    }
                    // Any OTHER interpreted operator (abs, div, mod, /,
                    // to_real, to_int, is_int, BV ops, ...) must NEVER be
                    // classified as an uninterpreted table symbol: treating an
                    // interpreted symbol's pinned semantics as freely choosable
                    // is a wrong-SAT (e.g. `forall x. (= (abs x) 0)` with a
                    // fabricated `abs := λ_.0`). Only the exact evaluator's
                    // whitelist above is in class; every other interpreted
                    // family is out.
                    if is_pure_arith_bool_symbol(name) || is_interpreted_bv_symbol(name) {
                        return None;
                    }
                    // Uninterpreted application.
                    if !is_mbqi_completable_uf_symbol(name)
                        || self.symbol_is_datatype_selector_or_constructor(name)
                    {
                        return None;
                    }
                    // CCMC M1: curried finite-table application. Admit
                    // `f(g1..gn, x)` where the TRAILING argument is the BARE
                    // binder and every PREFIX argument `gi` is binder-free
                    // (x-free) AND Int/Real-sorted (value-keyed rows are built
                    // in `finite_table_collect`; Seq-sorted prefixes are
                    // deferred to M3 and rejected here). The classic unary
                    // `f(x)` is the `n = 0` case (empty prefix). Any binder in a
                    // non-trailing position (`f(x, 3)`, `h(x, x)`), a shifted
                    // trailing arg (`f(g, x+1)`), or `f(g(x))` MISSES this shape
                    // and falls through to the x-under-argument guard below,
                    // which rejects it VERBATIM.
                    let is_table_app = match args.split_last() {
                        Some((&last, prefix)) => {
                            matches!(self.ctx.terms.get(last),
                                     TermData::Var(n, _) if n == var_name)
                                && prefix.iter().all(|&p| {
                                    !xdep.contains(&p)
                                        && matches!(self.ctx.terms.sort(p), Sort::Int | Sort::Real)
                                })
                        }
                        None => false,
                    };
                    if is_table_app {
                        let arg_sorts: Vec<Sort> = args
                            .iter()
                            .map(|&arg| self.ctx.terms.sort(arg).clone())
                            .collect();
                        match table_arg_sorts.get(name) {
                            Some(existing) if existing != &arg_sorts => return None,
                            Some(_) => {}
                            None => {
                                table_arg_sorts.insert(name.to_string(), arg_sorts);
                            }
                        }
                        let codomain = match self.ctx.terms.sort(t) {
                            Sort::Bool => TableCertSort::Bool,
                            Sort::Int => TableCertSort::Int,
                            Sort::Real => TableCertSort::Real,
                            // Unreachable (sort-admission check above), but
                            // fail closed rather than panic.
                            _ => return None,
                        };
                        match table_syms.get(name) {
                            Some(&cs) if cs != codomain => return None,
                            Some(_) => {}
                            None => {
                                table_syms.insert(name.to_string(), codomain);
                            }
                        }
                        body_syms.insert(name.to_string());
                        continue;
                    }
                    if args.iter().any(|a| xdep.contains(a)) {
                        // x under a UF argument in any shape other than the
                        // bare f(x): f(g(x)), f(x+1), h(x,x), ...
                        return None;
                    }
                    // Ground UF application: a model-pinned constant. Its
                    // arguments still must lie in the scanned fragment.
                    stack.extend(args.iter().copied());
                }
                // Let, nested quantifiers, anything else: out of class.
                _ => return None,
            }
        }
        Some(())
    }

    /// Collect the finite tables: every ground application `f(t)` of a table
    /// symbol anywhere in the snapshot, mapped `eval_M(t) -> eval_M(f(t))`.
    /// `None` on non-unary occurrences, unevaluable points, value conflicts,
    /// or table-size overflow.
    ///
    /// Runs AFTER every forall body passed [`Self::finite_table_scan_body`],
    /// so inside a certified body the ONLY variable is that forall's binder,
    /// and the only binder-dependent table shape is the bare `f(binder)`.
    /// Ground assertions, however, may contain FREE `Var` nodes (skolem
    /// constants): `f(sk)` there is a genuine ground application whose point
    /// must be collected — a bare-`Var` argument is skipped ONLY when it is
    /// the enclosing forall's binder (name match, the engine's substitution
    /// convention).
    fn finite_table_collect(
        &self,
        model: &Model,
        snapshot: &[TermId],
        table_syms: &HashMap<String, TableCertSort>,
    ) -> Option<HashMap<String, HashMap<TableCertKey, TableCertVal>>> {
        let mut tables: HashMap<String, HashMap<TableCertKey, TableCertVal>> = HashMap::default();
        for name in table_syms.keys() {
            tables.insert(name.clone(), HashMap::default());
        }
        let mut total_points = 0usize;
        for &root in snapshot {
            // Top-level binder context: certified snapshots have quantifiers
            // only as top-level single-binder foralls (checked in step 1/2 of
            // the certificate; anything else fails closed here).
            let (binder, walk_root): (Option<String>, TermId) = match self.ctx.terms.get(root) {
                TermData::Forall(vars, body, _) => {
                    if vars.len() != 1 {
                        return None;
                    }
                    (Some(vars[0].0.clone()), *body)
                }
                _ => (None, root),
            };
            let mut visited: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = vec![walk_root];
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::App(sym, args) => {
                        stack.extend(args.iter().copied());
                        let name = sym.name();
                        if !table_syms.contains_key(name) {
                            continue;
                        }
                        // CCMC M1: split the TRAILING point arg from the ground
                        // prefix. `f()` (no args) is outside the certified
                        // curried shape — fail closed.
                        let (&point_arg, prefix_args) = args.split_last()?;
                        // The binder may occur ONLY as the bare trailing point
                        // (the certified `f(g.., x)` body app); anywhere in the
                        // prefix is out of class (the scan rejects it) — fail
                        // closed rather than mis-collect.
                        if let Some(b) = binder.as_deref() {
                            if prefix_args
                                .iter()
                                .any(|&p| self.finite_table_mentions_var(p, b))
                            {
                                return None;
                            }
                        }
                        let is_binder_app = match (&binder, self.ctx.terms.get(point_arg)) {
                            (Some(b), TermData::Var(n, _)) => n == b,
                            _ => false,
                        };
                        if is_binder_app {
                            // f(g.., x) over the enclosing binder — certified by
                            // the pointwise + residual legs, not a table point.
                            continue;
                        }
                        if binder
                            .as_deref()
                            .is_some_and(|b| self.finite_table_mentions_var(point_arg, b))
                        {
                            // Binder under a compound trailing arg (`f(g.., x+1)`):
                            // out of class (the scan rejects it) — fail closed.
                            return None;
                        }
                        // Ground application `f(c1..cn, cx)` (possibly over free
                        // skolem variables — the model pins those): a
                        // VALUE-KEYED table point `(prefix vals, cx)`. Prefix
                        // and point must be EXACT rationals of their sorts. An
                        // `EvalValue::Unknown`/`Algebraic` (irrational real from
                        // an NRA-shaped ground part) anywhere has no exact
                        // `BigRational` key and fails closed.
                        let mut prefix_key: Vec<num_rational::BigRational> =
                            Vec::with_capacity(prefix_args.len());
                        for &p in prefix_args {
                            prefix_key.push(self.finite_table_prefix_value(model, p)?);
                        }
                        let point = self.finite_table_prefix_value(model, point_arg)?;
                        let key: TableCertKey = (prefix_key, point);
                        // Classify the value by the DECLARED codomain kind
                        // (established by the body scan) so table entries,
                        // defaults, and evaluator results stay kind-aligned.
                        let val = match (table_syms.get(name)?, self.evaluate_term(model, t)) {
                            (TableCertSort::Real, EvalValue::Rational(r)) => TableCertVal::Rat(r),
                            (TableCertSort::Int, EvalValue::Rational(r)) if r.is_integer() => {
                                TableCertVal::Int(r.numer().clone())
                            }
                            (TableCertSort::Bool, EvalValue::Bool(b)) => TableCertVal::Bool(b),
                            _ => return None,
                        };
                        let table = tables.get_mut(name)?;
                        match table.get(&key) {
                            Some(existing) if *existing != val => return None,
                            Some(_) => {}
                            None => {
                                total_points += 1;
                                if total_points > MAX_TABLE_CERT_POINTS_TOTAL {
                                    return None;
                                }
                                table.insert(key, val);
                            }
                        }
                    }
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    TermData::Let(bindings, b) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*b);
                    }
                    // A quantifier below the top level is out of class.
                    TermData::Forall(..) | TermData::Exists(..) => return None,
                    _ => {}
                }
            }
        }
        Some(tables)
    }

    /// Exact evaluation of a certified forall body at binder value `point`
    /// under the constructed interpretation `M'` (tables + defaults for the
    /// table symbols, the candidate model `M` for every x-free subterm).
    /// Returns `None` whenever any subterm's value is not definite.
    #[allow(clippy::too_many_arguments)]
    fn finite_table_eval(
        &self,
        model: &Model,
        t: TermId,
        var_name: &str,
        var_sort: &Sort,
        point: &num_rational::BigRational,
        xdep: &HashSet<TermId>,
        tables: &HashMap<String, HashMap<TableCertKey, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
    ) -> Option<TableCertVal> {
        use num_bigint::BigInt;
        // x-free subterms evaluate identically under M and M' (see the
        // totality argument): delegate to the model evaluator and demand a
        // definite value.
        if !xdep.contains(&t) {
            return match self.evaluate_term(model, t) {
                EvalValue::Bool(b) => Some(TableCertVal::Bool(b)),
                // Kind-by-sort: a Real-sorted subterm becomes an exact
                // rational (even when integer-valued), an Int-sorted one an
                // integer. Numeric comparisons below promote Int to rational,
                // so the kinds never lose exactness.
                EvalValue::Rational(r) => match self.ctx.terms.sort(t) {
                    Sort::Real => Some(TableCertVal::Rat(r)),
                    _ if r.is_integer() => Some(TableCertVal::Int(r.numer().clone())),
                    _ => None,
                },
                _ => None,
            };
        }
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
            match self.ctx.terms.get(t) {
                // The binder value carries the BINDER's sort kind: an exact
                // integer for an `Int` binder (points are integer-valued by
                // construction; fail closed otherwise), an exact rational for
                // a `Real` binder.
                TermData::Var(n, _) if n == var_name => match var_sort {
                    Sort::Int if point.is_integer() => {
                        Some(TableCertVal::Int(point.numer().clone()))
                    }
                    Sort::Real => Some(TableCertVal::Rat(point.clone())),
                    _ => None,
                },
                TermData::Not(i) => {
                    match self.finite_table_eval(
                        model, *i, var_name, var_sort, point, xdep, tables, defaults,
                    )? {
                        TableCertVal::Bool(b) => Some(TableCertVal::Bool(!b)),
                        TableCertVal::Int(_) | TableCertVal::Rat(_) => None,
                    }
                }
                TermData::Ite(c, a, b) => {
                    match self.finite_table_eval(
                        model, *c, var_name, var_sort, point, xdep, tables, defaults,
                    )? {
                        TableCertVal::Bool(true) => self.finite_table_eval(
                            model, *a, var_name, var_sort, point, xdep, tables, defaults,
                        ),
                        TableCertVal::Bool(false) => self.finite_table_eval(
                            model, *b, var_name, var_sort, point, xdep, tables, defaults,
                        ),
                        TableCertVal::Int(_) | TableCertVal::Rat(_) => None,
                    }
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    let args = args.clone();
                    // Table application f(g1..gn, x): the scan guarantees the
                    // only x-dependent UF shape is the curried bare-trailing-
                    // binder app (the prefix is x-free). Evaluate the prefix
                    // under M into the value-key row — the SAME keying as
                    // `finite_table_collect` — then look up `(prefix, point)`
                    // with the per-symbol default as the fallback for the
                    // default region.
                    if tables.contains_key(name)
                        && args.split_last().is_some_and(|(&last, _)| {
                            matches!(self.ctx.terms.get(last),
                                     TermData::Var(n, _) if n == var_name)
                        })
                    {
                        let (_, prefix_args) = args.split_last()?;
                        let table = tables.get(name)?;
                        let mut prefix_key: Vec<num_rational::BigRational> =
                            Vec::with_capacity(prefix_args.len());
                        for &p in prefix_args {
                            prefix_key.push(self.finite_table_prefix_value(model, p)?);
                        }
                        let key: TableCertKey = (prefix_key, point.clone());
                        return match table.get(&key) {
                            Some(v) => Some(v.clone()),
                            None => defaults.get(name).cloned(),
                        };
                    }
                    // Interpreted operators, evaluated exactly over BigInt.
                    let mut vals: Vec<TableCertVal> = Vec::with_capacity(args.len());
                    for &a in &args {
                        vals.push(self.finite_table_eval(
                            model, a, var_name, var_sort, point, xdep, tables, defaults,
                        )?);
                    }
                    let all_bool = |vals: &[TableCertVal]| -> Option<Vec<bool>> {
                        vals.iter()
                            .map(|v| match v {
                                TableCertVal::Bool(b) => Some(*b),
                                TableCertVal::Int(_) | TableCertVal::Rat(_) => None,
                            })
                            .collect()
                    };
                    let all_int = |vals: &[TableCertVal]| -> Option<Vec<BigInt>> {
                        vals.iter()
                            .map(|v| match v {
                                TableCertVal::Int(i) => Some(i.clone()),
                                TableCertVal::Bool(_) | TableCertVal::Rat(_) => None,
                            })
                            .collect()
                    };
                    // Exact numeric view: Int promotes losslessly to
                    // BigRational (Int(5) and Rat(5) denote the same number
                    // under SMT-LIB's Int-to-Real coercion), Bool is not
                    // numeric. All arithmetic on this view is exact.
                    let as_rat = |v: &TableCertVal| -> Option<num_rational::BigRational> {
                        match v {
                            TableCertVal::Int(i) => {
                                Some(num_rational::BigRational::from_integer(i.clone()))
                            }
                            TableCertVal::Rat(r) => Some(r.clone()),
                            TableCertVal::Bool(_) => None,
                        }
                    };
                    let all_num =
                        |vals: &[TableCertVal]| -> Option<Vec<num_rational::BigRational>> {
                            vals.iter().map(as_rat).collect()
                        };
                    let any_rat = |vals: &[TableCertVal]| {
                        vals.iter().any(|v| matches!(v, TableCertVal::Rat(_)))
                    };
                    match name {
                        "and" => Some(TableCertVal::Bool(all_bool(&vals)?.iter().all(|&b| b))),
                        "or" => Some(TableCertVal::Bool(all_bool(&vals)?.iter().any(|&b| b))),
                        "not" => {
                            let bs = all_bool(&vals)?;
                            if bs.len() != 1 {
                                return None;
                            }
                            Some(TableCertVal::Bool(!bs[0]))
                        }
                        "=>" => {
                            let bs = all_bool(&vals)?;
                            if bs.is_empty() {
                                return None;
                            }
                            // Right-associative chain: false anywhere before
                            // the last argument makes it true.
                            let value = bs[..bs.len() - 1].iter().any(|&b| !b) || bs[bs.len() - 1];
                            Some(TableCertVal::Bool(value))
                        }
                        "xor" => {
                            let bs = all_bool(&vals)?;
                            Some(TableCertVal::Bool(bs.iter().fold(false, |acc, &b| acc ^ b)))
                        }
                        "=" => {
                            if vals.len() < 2 {
                                return None;
                            }
                            if vals.iter().all(|v| matches!(v, TableCertVal::Bool(_))) {
                                return Some(TableCertVal::Bool(
                                    vals.windows(2).all(|w| w[0] == w[1]),
                                ));
                            }
                            // Numeric chain: compare exactly as rationals
                            // (Int promotes losslessly; mixed Bool/numeric
                            // fails closed inside all_num).
                            let ns = all_num(&vals)?;
                            Some(TableCertVal::Bool(ns.windows(2).all(|w| w[0] == w[1])))
                        }
                        "distinct" => {
                            if vals.len() < 2 {
                                return None;
                            }
                            if vals.iter().all(|v| matches!(v, TableCertVal::Bool(_))) {
                                let mut ok = true;
                                for i in 0..vals.len() {
                                    for j in (i + 1)..vals.len() {
                                        if vals[i] == vals[j] {
                                            ok = false;
                                        }
                                    }
                                }
                                return Some(TableCertVal::Bool(ok));
                            }
                            let ns = all_num(&vals)?;
                            let mut ok = true;
                            for i in 0..ns.len() {
                                for j in (i + 1)..ns.len() {
                                    if ns[i] == ns[j] {
                                        ok = false;
                                    }
                                }
                            }
                            Some(TableCertVal::Bool(ok))
                        }
                        "<" | "<=" | ">" | ">=" => {
                            let ns = all_num(&vals)?;
                            if ns.len() < 2 {
                                return None;
                            }
                            let ok = ns.windows(2).all(|w| match name {
                                "<" => w[0] < w[1],
                                "<=" => w[0] <= w[1],
                                ">" => w[0] > w[1],
                                _ => w[0] >= w[1],
                            });
                            Some(TableCertVal::Bool(ok))
                        }
                        "+" => {
                            if any_rat(&vals) {
                                let ns = all_num(&vals)?;
                                return Some(TableCertVal::Rat(ns.into_iter().sum()));
                            }
                            let is = all_int(&vals)?;
                            Some(TableCertVal::Int(is.into_iter().sum()))
                        }
                        "-" => {
                            if any_rat(&vals) {
                                let ns = all_num(&vals)?;
                                return match ns.len() {
                                    0 => None,
                                    1 => Some(TableCertVal::Rat(-ns[0].clone())),
                                    _ => {
                                        let mut acc = ns[0].clone();
                                        for v in &ns[1..] {
                                            acc -= v;
                                        }
                                        Some(TableCertVal::Rat(acc))
                                    }
                                };
                            }
                            let is = all_int(&vals)?;
                            match is.len() {
                                0 => None,
                                1 => Some(TableCertVal::Int(-is[0].clone())),
                                _ => {
                                    let mut acc = is[0].clone();
                                    for v in &is[1..] {
                                        acc -= v;
                                    }
                                    Some(TableCertVal::Int(acc))
                                }
                            }
                        }
                        "*" => {
                            if any_rat(&vals) {
                                let ns = all_num(&vals)?;
                                let mut acc =
                                    num_rational::BigRational::from_integer(BigInt::from(1));
                                for v in ns {
                                    acc *= v;
                                }
                                return Some(TableCertVal::Rat(acc));
                            }
                            let is = all_int(&vals)?;
                            let mut acc = BigInt::from(1);
                            for v in is {
                                acc *= v;
                            }
                            Some(TableCertVal::Int(acc))
                        }
                        "/" => {
                            // Real division; the scan admits it only with
                            // literal NONZERO divisors — re-check here anyway
                            // (belt and braces: a zero divisor's semantics is
                            // unpinned, so fail closed rather than compute).
                            use num_traits::Zero;
                            let ns = all_num(&vals)?;
                            if ns.len() < 2 {
                                return None;
                            }
                            let mut acc = ns[0].clone();
                            for d in &ns[1..] {
                                if d.is_zero() {
                                    return None;
                                }
                                acc /= d;
                            }
                            Some(TableCertVal::Rat(acc))
                        }
                        "to_real" => {
                            // Exact Int -> Real injection (identity on the
                            // rational view; no rounding surface).
                            if vals.len() != 1 {
                                return None;
                            }
                            Some(TableCertVal::Rat(as_rat(&vals[0])?))
                        }
                        "ite" => {
                            if vals.len() != 3 {
                                return None;
                            }
                            match &vals[0] {
                                TableCertVal::Bool(true) => Some(vals[1].clone()),
                                TableCertVal::Bool(false) => Some(vals[2].clone()),
                                TableCertVal::Int(_) | TableCertVal::Rat(_) => None,
                            }
                        }
                        // Any other x-dependent application is out of class —
                        // the scan should have rejected it; fail closed.
                        _ => None,
                    }
                }
                TermData::Const(Constant::Int(v)) => Some(TableCertVal::Int(v.clone())),
                TermData::Const(Constant::Rational(w)) => Some(TableCertVal::Rat(w.0.clone())),
                TermData::Const(Constant::Bool(b)) => Some(TableCertVal::Bool(*b)),
                _ => None,
            }
        })
    }

    /// Build the RESIDUAL of a certified body: every table application `f(x)`
    /// replaced by its default constant; everything x-free left intact.
    fn finite_table_residual(
        &mut self,
        t: TermId,
        var_name: &str,
        xdep: &HashSet<TermId>,
        defaults: &HashMap<String, TableCertVal>,
        memo: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        if !xdep.contains(&t) {
            return Some(t);
        }
        if let Some(&r) = memo.get(&t) {
            return Some(r);
        }
        let result = match self.ctx.terms.get(t).clone() {
            TermData::Var(ref n, _) if n == var_name => t,
            TermData::Not(i) => {
                let ri = self.finite_table_residual(i, var_name, xdep, defaults, memo)?;
                self.ctx.terms.mk_not(ri)
            }
            TermData::Ite(c, a, b) => {
                let rc = self.finite_table_residual(c, var_name, xdep, defaults, memo)?;
                let ra = self.finite_table_residual(a, var_name, xdep, defaults, memo)?;
                let rb = self.finite_table_residual(b, var_name, xdep, defaults, memo)?;
                self.ctx.terms.mk_ite(rc, ra, rb)
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                // CCMC M1: a curried table application `f(g1..gn, x)` in the
                // default region collapses to the symbol's single default
                // constant `d_f`. The prefix is x-free (guarded here for
                // defense-in-depth, matching the scan/collect/eval sites), so
                // for every `x` outside the pointwise set
                // `M'(f)(prefix, x) = d_f` — see the residual leg of the
                // totality argument.
                let is_table_app = args.split_last().is_some_and(|(&last, prefix)| {
                    matches!(self.ctx.terms.get(last), TermData::Var(n, _) if n == var_name)
                        && prefix.iter().all(|&p| !xdep.contains(&p))
                });
                if defaults.contains_key(name) && is_table_app {
                    match defaults.get(name)? {
                        TableCertVal::Int(v) => self.ctx.terms.mk_int(v.clone()),
                        TableCertVal::Rat(r) => self.ctx.terms.mk_rational(r.clone()),
                        TableCertVal::Bool(b) => self.ctx.terms.mk_bool(*b),
                    }
                } else {
                    let mut new_args: Vec<TermId> = Vec::with_capacity(args.len());
                    for a in args {
                        new_args
                            .push(self.finite_table_residual(a, var_name, xdep, defaults, memo)?);
                    }
                    let sort = self.ctx.terms.sort(t).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            // Let / quantifiers were rejected by the scan; fail closed.
            _ => return None,
        };
        memo.insert(t, result);
        Some(result)
    }

    /// True when `t` mentions a variable named `name` anywhere.
    fn finite_table_mentions_var(&self, t: TermId, name: &str) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Var(n, _) => {
                    if n == name {
                        return true;
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                _ => {}
            }
        }
        false
    }

    // NOTE: a `finite_table_contains_any_var` (ANY-variable variant of the
    // check above) was authored alongside it in 0e7ca8fe but never wired to a
    // call site in any commit; the certificate's design deliberately admits
    // free `Var` nodes as model-pinned skolem constants (see
    // `finite_table_scan_body` / `finite_table_collect`), so no
    // residual-with-foreign-vars gate exists to receive it. Deleted — recover
    // from git history if a caller ever materializes.

    /// Collect Rational constants syntactically present in `t` (bounded use:
    /// Real-codomain default-candidate hints only — never a soundness
    /// surface; every candidate is fully re-verified by the pointwise +
    /// residual legs).
    fn finite_table_collect_rat_consts(&self, t: TermId, out: &mut Vec<num_rational::BigRational>) {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if out.len() >= 16 {
                return;
            }
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Const(Constant::Rational(w)) => out.push(w.0.clone()),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }

    /// Collect Int constants syntactically present in `t` (bounded use:
    /// default-candidate hints only — never a soundness surface).
    fn finite_table_collect_int_consts(&self, t: TermId, out: &mut Vec<num_bigint::BigInt>) {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if out.len() >= 16 {
                return;
            }
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Const(Constant::Int(v)) => out.push(v.clone()),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }

    // =====================================================================
    // DT-MBQI-Sat certificate — F4 piecewise-lemma route + e-class completion
    // (M1 of the DT-MBQI-Sat campaign; grant-only, `AY_DT_CERT`-gated).
    //
    // Certifies `Sat` for a quantifier-incompleteness `Unknown` when EVERY
    // top-level snapshot `forall` binds exactly ONE `Sort::Datatype` variable
    // and reads that binder ONLY as the DIRECT argument of a finite-piecewise
    // UF (the "cell-invariance" shape `forall x:DT. atom-over-{uf(x)}`). The
    // datatype binder STAYS MBQI-unsafe (`is_mbqi_unsafe_binder_sort` still
    // matches `Sort::Datatype`); this certificate is the sole sanctioned path
    // and is consulted only from the Phase-2.5/3.5 grant arms.
    //
    // SOUNDNESS (grant-only; every uncertain path DECLINES = returns `None`):
    //   * ALL-OR-NOTHING: any `forall` that is not a single-`Datatype`-binder
    //     F4 body makes the whole snapshot out of class (so mixed/bridge/Int
    //     snapshots — repro_fullsort, adv1/2/3 — decline).
    //   * E-CLASS COMPLETION obligation: each finite-table row is keyed by the
    //     ARGUMENT's committed e-class (EUF `term_values`), so congruent apps
    //     share a row (a value disagreement there is a detected conflict, not
    //     two vacuous rows). INJECTIVITY/DISEQ-RESPECT: two DISTINCT e-classes
    //     that materialize (via ctor-app or asserted tester+selector facts) to
    //     the SAME constructor normal form are a collapse — DECLINE (the
    //     distinct-collapse wrong-SAT vector).
    //   * F4 EVALUATION: the atom is checked at EVERY table row (exception
    //     leaf) AND at the JOINT DEFAULT CELL (a datatype element outside every
    //     table's key set — cell-invariance makes the substituted body x-free,
    //     so ONE default-cell check covers all unobserved elements). All
    //     arithmetic is exact (`evaluate_term` over `BigRational`).
    //   * TRI-STATE CARDINALITY: recursive/infinite-scalar-field ⇒ infinite
    //     (default cell non-empty, checked); all-nullary ⇒ finite/exhaustive;
    //     otherwise DECLINE.
    //   * STAGE-5 GROUND RE-VERIFICATION: EVERY ground assertion must evaluate
    //     to a definite `Bool(true)` under the completed model `M'`. M1 does no
    //     F3 default rewriting, so `M'` equals `M` on every ground term (the
    //     completion only assigns table UFs a fresh default OUTSIDE their
    //     observed points); the single-authority check therefore reads the one
    //     model — never `self.last_model` behind a stale interpretation.
    // This function ONLY ever GRANTS a `Sat`; it never influences an UNSAT.
    pub(in crate::executor) fn try_dt_model_sat_certificate(
        &mut self,
        snapshot: &[TermId],
        _category: LogicCategory,
    ) -> Option<CheckedDtSatAuthority> {
        use num_bigint::BigInt;

        // AY_DT_CERT gate. Off => byte-identical (no clone, no mint, no log).
        let mode = dt_cert_mode();
        if matches!(mode, DtCertMode::Off) {
            return None;
        }
        if self.external_stop_reason().is_some() {
            return None;
        }
        let model = self.last_model.clone()?;

        // ---- 1. Partition; reject any non-top-level-forall quantifier. ----
        let mut foralls: Vec<TermId> = Vec::new();
        let mut grounds: Vec<TermId> = Vec::new();
        for &a in snapshot {
            match self.ctx.terms.get(a) {
                TermData::Forall(..) => foralls.push(a),
                _ if contains_quantifier(&self.ctx.terms, a) => {
                    dt_cert_note(mode, "decline: nested/non-top-level quantifier");
                    return None;
                }
                _ => grounds.push(a),
            }
        }
        if foralls.is_empty() {
            return None;
        }

        // ---- 2. MULTI-ROUTE classification over EVERY forall (all-or-nothing). ----
        // M4: each `forall` must fall in ONE of the four sanctioned routes:
        //   F4 — single DT-binder cell-invariant `forall x:DT. atom-over-{uf(x)}`.
        //   G  — ground-reduction `forall a,b. t = C(a,b) => phi` with `t` GROUND
        //        (DT injectivity pins (a,b) uniquely at (sel_i t)).
        //   F2 — DT-selector tautology `sel_i(C(a,b)) = a` (theory-tautology).
        //   F3 — bridge symbolic-default `is-C(x) => uf(x) = sel(x)` (uf ≡ sel).
        // ANY forall matching NONE makes the whole snapshot decline (unchanged
        // all-or-nothing discipline — now over four routes, not one).
        struct DtForallInfo {
            var_name: String,
            body: TermId,
            body_syms: Vec<String>,
        }
        // uf name -> codomain kind (Int/Real/Bool).
        let mut table_syms: HashMap<String, TableCertSort> = HashMap::default();
        // Exact F4 source heads/signatures.  The compact string-keyed table
        // maps below are authoritative only after these requests are bound to
        // live ordinary free-UF declarations and every occurrence is audited.
        let mut table_requests: HashMap<String, ay_frontend::ProjectionBindingRequest> =
            HashMap::default();
        let mut infos: Vec<DtForallInfo> = Vec::with_capacity(foralls.len());
        // G-route foralls (ground-reduction; verified against M' below).
        let mut g_infos: Vec<GCertInfo> = Vec::new();
        // F3 bridge pairs (bridge-UF name, declared-selector name).
        let mut f3_pairs: Vec<(String, String)> = Vec::new();
        // Exact F3/W1 bridge source heads/signatures.  A name-based structural
        // match may nominate a candidate, but only one of these positively
        // checked requests may authorize rewriting that head as a selector.
        let mut bridge_requests: HashMap<String, ay_frontend::ProjectionBindingRequest> =
            HashMap::default();
        // F4 bodies, for the bridge-freeness soundness gate below.
        let mut f4_bodies: Vec<TermId> = Vec::new();
        // W1 bridge-route structural claims (forall index, bridge-UF name,
        // constructor, field index) — certified ONLY by the mandatory
        // selector-bridge-premise gate in step 2c below (`AY_DT_CERT_BRIDGE_ROUTE`,
        // SHADOW-ONLY in this increment: a claim can never reach a grant).
        let bridge_route = dt_cert_bridge_route_enabled();
        let mut bridge_claims: Vec<(usize, String, String, usize)> = Vec::new();
        for (qi, &q) in foralls.iter().enumerate() {
            if self.ctx.terms.is_no_mbqi(q) {
                dt_cert_note(mode, "decline: no_mbqi forall");
                return None;
            }
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(vars, body, _) => (vars.clone(), *body),
                _ => return None,
            };
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

            // Frontend datatype reduction can prove an authored selector-over-
            // constructor axiom while elaborating it, leaving the exact query
            // root as `forall (...). true`. That root is already a
            // model-independent tautology; requiring the unreduced F2 shape
            // would make certification depend on whether preprocessing happened
            // before the root snapshot was taken. Accept only the literal core
            // `true` here—never an evaluator guess or a repeated solve.
            if body == self.ctx.terms.true_term() {
                continue;
            }

            // Route F2: DT-selector tautology (model-independent).
            if self.dt_cert_classify_f2(&var_names, body).is_some() {
                continue;
            }
            // Route W1 (`AY_DT_CERT_BRIDGE_ROUTE`): bridge-UF-over-constructor
            // tautology `bridge(C(v0..vk)) = v_i` — the F2 analog over a FREE
            // bridge UF. The structural match alone is NOT sound; the claim is
            // DEFERRED to the mandatory selector-bridge-premise gate (step 2c),
            // because the certifying F3 pin forall may appear anywhere in the
            // snapshot (before or after this one).
            if bridge_route {
                if let Some((bridge, ctor, idx)) = self.dt_cert_classify_f2_bridge(&var_names, body)
                {
                    let request = self.dt_cert_projection_request(body, &bridge)?;
                    match bridge_requests.get(&bridge) {
                        Some(existing) if existing != &request => {
                            dt_cert_note(
                                mode,
                                "decline: bridge head has inconsistent exact signatures",
                            );
                            return None;
                        }
                        Some(_) => {}
                        None => {
                            bridge_requests.insert(bridge.clone(), request);
                        }
                    }
                    bridge_claims.push((qi, bridge, ctor, idx));
                    continue;
                }
            }
            // Route F3: bridge symbolic-default closure.
            if let Some((bridge, sel)) = self.dt_cert_classify_f3(&var_names, body) {
                let request = self.dt_cert_projection_request(body, &bridge)?;
                match bridge_requests.get(&bridge) {
                    Some(existing) if existing != &request => {
                        dt_cert_note(
                            mode,
                            "decline: bridge head has inconsistent exact signatures",
                        );
                        return None;
                    }
                    Some(_) => {}
                    None => {
                        bridge_requests.insert(bridge.clone(), request);
                    }
                }
                f3_pairs.push((bridge, sel));
                continue;
            }
            // Route G: Cons-guarded ground reduction.
            if let Some(gi) = self.dt_cert_classify_g(&var_names, body) {
                g_infos.push(gi);
                continue;
            }

            // Route F4: single DT-binder cell-invariant (the M1 path).
            if vars.len() != 1 {
                dt_cert_note(mode, "decline: forall is not single-binder");
                return None;
            }
            let Some(dt_name) = self.dt_cert_sort_name(&vars[0].1) else {
                dt_cert_note(mode, "decline: binder is not a Datatype sort");
                return None;
            };
            let var_name = var_names[0].clone();
            let xdep = self.finite_table_xdep_nodes(body, &var_name);
            let mut body_syms: HashSet<String> = HashSet::default();
            if self
                .dt_cert_scan_body(
                    body,
                    &var_name,
                    &xdep,
                    &mut table_syms,
                    &mut table_requests,
                    &mut body_syms,
                )
                .is_none()
            {
                dt_cert_note(mode, "decline: forall body out of F4 cell-invariant class");
                return None;
            }
            if body_syms.is_empty() {
                // No table UF reads the binder: the body cannot depend on x in
                // the certified way — out of class.
                dt_cert_note(mode, "decline: forall body has no table UF over binder");
                return None;
            }
            let mut body_syms: Vec<String> = body_syms.into_iter().collect();
            body_syms.sort_unstable();
            // TRI-STATE cardinality (item 4).
            if self.dt_cert_cardinality(&dt_name).is_none() {
                dt_cert_note(mode, "decline: unclassifiable datatype cardinality");
                return None;
            }
            infos.push(DtForallInfo {
                var_name,
                body,
                body_syms,
            });
            f4_bodies.push(body);
        }

        // ---- 2b. Build the F3 bridge rewrite (uf ≡ selector) + soundness gates. ----
        // The completed model M' interprets each bridge UF AS its datatype
        // selector (the z3-proven mandatory symbolic default). Every semantic
        // obligation below (grounds, G claims, F4 cells) is discharged against
        // THIS single completed M' — never a pre-rewrite model (adv3 discipline).
        let mut bridge_rewrite: HashMap<String, (String, Sort)> = HashMap::default();
        for (bridge, sel) in &f3_pairs {
            let Some(field_sort) = self.dt_cert_selector_field_sort(sel) else {
                dt_cert_note(mode, "decline: F3 selector has no declared field sort");
                return None;
            };
            match bridge_rewrite.get(bridge) {
                Some((s, _)) if s != sel => {
                    dt_cert_note(mode, "decline: bridge UF mapped to two selectors");
                    return None;
                }
                _ => {
                    bridge_rewrite.insert(bridge.clone(), (sel.clone(), field_sort));
                }
            }
        }
        // ---- 2c. W1 bridge-route MANDATORY selector-bridge-premise gate. ----
        // A claimed bridge tautology `forall v0..vk. bridge(C(v..)) = v_i` is
        // certified ONLY by COMPOSITION: the completed model M' interprets
        // `bridge` AS its F3-pinned selector (bridge_rewrite), under which the
        // body IS the native selector tautology `sel_i(C(v..)) = v_i` — an F2
        // theory tautology — iff the pinned selector is EXACTLY `C`'s declared
        // field-`i` selector. A bridge with NO in-snapshot F3 pin is genuinely
        // free: its "tautology" is an unverified constraint and claiming it
        // would be a wrong-grant (the wrong-SAT vector) — DECLINE, fail-closed.
        // Same for a pin to a different selector (the rewritten body would not
        // be a tautology).
        let bridge_route_used = !bridge_claims.is_empty();
        for (qi, bridge, ctor, idx) in &bridge_claims {
            match self.dt_cert_bridge_claim_check(&bridge_rewrite, bridge, ctor, *idx) {
                Err(reason) => {
                    dt_cert_note(
                        mode,
                        &format!("[BRIDGE-ROUTE] decline: forall {qi} {reason}"),
                    );
                    return None;
                }
                Ok(pinned_sel) => {
                    dt_cert_note(
                        mode,
                        &format!(
                            "[BRIDGE-ROUTE] would-claim forall {qi} \
                             (`{bridge}`(({ctor} ..)) = field {idx}) via bridge pin \
                             `{bridge}`=`{pinned_sel}`"
                        ),
                    );
                }
            }
        }
        // A bridge UF must NOT also be an F4 finite-table symbol (a completion
        // conflict — one symbol, two completions).
        for b in bridge_rewrite.keys() {
            if table_syms.contains_key(b) {
                dt_cert_note(mode, "decline: symbol is both an F3 bridge and an F4 table");
                return None;
            }
        }

        // Positive source authority for every F4 table and F3/W1 bridge head.
        // The recognizers above are deliberately only structural classifiers;
        // they cannot establish that a spelling denotes a free function rather
        // than a definition, datatype member, built-in, overloaded declaration,
        // indexed/internal symbol, or a declaration from a stale scope.  Bind
        // each exact head/signature to its live source declaration and audit
        // every same-spelling occurrence across the complete snapshot before
        // any model completion or selector rewrite can contribute to SAT.
        if table_requests.len() != table_syms.len() || bridge_requests.len() != bridge_rewrite.len()
        {
            dt_cert_note(
                mode,
                "decline: incomplete datatype projection source bindings",
            );
            return None;
        }
        let mut projection_requests: Vec<ay_frontend::ProjectionBindingRequest> = table_requests
            .into_values()
            .chain(bridge_requests.into_values())
            .collect();
        projection_requests.sort_by(|a, b| a.symbol.name().cmp(b.symbol.name()));
        let checked_projection_bindings = if projection_requests.is_empty() {
            Vec::new()
        } else {
            let Some(bindings) =
                self.check_table_declaration_occurrences(snapshot, &projection_requests)
            else {
                dt_cert_note(
                    mode,
                    "decline: datatype projection head lacks exact live free-UF authority",
                );
                return None;
            };
            bindings
        };
        // The M1 F4 cell machinery evaluates WITHOUT the bridge rewrite; keep it
        // rewrite-free & sound by declining any F4 body that reads a bridge UF.
        if !bridge_rewrite.is_empty() {
            for &b in &f4_bodies {
                if self.dt_cert_term_mentions_bridge(b, &bridge_rewrite) {
                    dt_cert_note(mode, "decline: F4 body reads a rewritten bridge UF");
                    return None;
                }
            }
        }

        // Asserted tester/selector ground facts (drive the G-route tester
        // fallback + the injectivity materialization).
        let (tester_idx, sel_idx) = self.dt_cert_index_ground_facts(&grounds);

        // ---- 3. STAGE-5 ground re-verification UNDER M' (bridge-rewritten). ----
        // W2 (bridge route) lazily-built argument-value congruence index over
        // the ground core's committed UF applications; see
        // `dt_cert_build_uf_value_index`.
        let mut uf_value_index: Option<HashMap<(String, Vec<String>), Option<(TermId, String)>>> =
            None;
        for (gi, &g) in grounds.iter().enumerate() {
            let mut memo: HashMap<TermId, TermId> = HashMap::default();
            let g2 = self.dt_cert_bridge_rewrite(g, &bridge_rewrite, &mut memo);
            let mut g_final = g2;
            let mut definite_true = matches!(self.evaluate_term(&model, g2), EvalValue::Bool(true))
                // W2a (bridge route, gated on an ACTIVE bridge claim so it can
                // only ever feed the shadow-withheld verdict): Kleene retry of
                // the boolean skeleton. `evaluate_term`'s `or`/`and` scans
                // bail to Unknown on the FIRST non-definite operand, so
                // `(or <selector-over-mismatched-ctor …> <true guard>)` reads
                // Unknown even though the guard decides it. Kleene semantics
                // are strictly sound (true iff a disjunct is true / all
                // conjuncts true), so this only RECOVERS definite verdicts —
                // it never manufactures one.
                || (bridge_route_used
                    && self.dt_cert_eval_ground_kleene(&model, g2) == Some(true));
            if !definite_true && bridge_route_used {
                // W2b (bridge route, same shadow containment): the bridge
                // rewrite MINTS fresh applications `uf(sel(t))` whose TermId
                // has no committed model value, while the pre-rewrite app
                // `uf(bridge(t))` HAS one and both arguments evaluate to the
                // SAME committed element. Under the ONE completed model M',
                // `eval(a) = eval(a')` (definite) implies `f(a) = f(a')` for
                // ANY function symbol `f` (function congruence) — so
                // substituting the committed pre-rewrite application for the
                // indefinite minted one preserves the M'-value exactly.
                // Conflicting committed rows for one (symbol, arg-values) key
                // poison that key (never used) — fail-closed.
                let index = uf_value_index
                    .get_or_insert_with(|| self.dt_cert_build_uf_value_index(&model, &grounds));
                let mut cmemo: HashMap<TermId, TermId> = HashMap::default();
                let g3 = self.dt_cert_congruence_rewrite(&model, g2, index, &mut cmemo);
                g_final = g3;
                definite_true = matches!(self.evaluate_term(&model, g3), EvalValue::Bool(true))
                    || self.dt_cert_eval_ground_kleene(&model, g3) == Some(true);
            }
            if !definite_true {
                if bridge_route {
                    // W2 measurement detail (additive, bridge-route-gated):
                    // WHICH ground failed and HOW (definite-false vs
                    // non-definite), so the model-completion gap is localized
                    // by index instead of re-derived by bisection.
                    let ev = self.evaluate_term(&model, g_final);
                    let kleene = if bridge_route_used {
                        self.dt_cert_eval_ground_kleene(&model, g_final)
                    } else {
                        None
                    };
                    dt_cert_note(
                        mode,
                        &format!(
                            "[BRIDGE-ROUTE] ground {gi} not definite-true under M': \
                             eval={ev:?} kleene={kleene:?}"
                        ),
                    );
                    // W2 residual diagnostic (decline path only, bounded):
                    // dump the failing ground's subterm evaluations so the
                    // exact indefinite leaf is visible without bisection —
                    // this is how the ground-5 congruence gap was localized,
                    // and it is the measurement tool for the next residual.
                    let mut stack = vec![(g_final, 0usize)];
                    let mut printed = 0usize;
                    while let Some((t, d)) = stack.pop() {
                        if printed > 60 {
                            break;
                        }
                        printed += 1;
                        let (kind, children): (String, Vec<TermId>) =
                            match self.ctx.terms.get(t).clone() {
                                TermData::App(sym, args) => {
                                    (format!("App({})", sym.name()), args.clone())
                                }
                                TermData::Var(n, _) => (format!("Var({n})"), vec![]),
                                TermData::Const(c) => (format!("Const({c:?})"), vec![]),
                                TermData::Not(i) => ("Not".to_string(), vec![i]),
                                TermData::Ite(c, a, b) => ("Ite".to_string(), vec![c, a, b]),
                                other => (format!("{other:?}"), vec![]),
                            };
                        let ev = self.evaluate_term(&model, t);
                        eprintln!(
                            "c CERT/dt-mbqi-sat [BRIDGE-ROUTE][W2-DBG] {:indent$}{kind} eval={ev:?}",
                            "",
                            indent = d * 2
                        );
                        for c in children.into_iter().rev() {
                            stack.push((c, d + 1));
                        }
                    }
                }
                dt_cert_note(
                    mode,
                    "decline: a ground assertion is not definite-true under M'",
                );
                return None;
            }
        }

        // ---- 3b. G-route: verify each ground-reduction forall under M'. ----
        for gi in &g_infos {
            match self.dt_cert_verify_g(&model, gi, &bridge_rewrite, &tester_idx, &sel_idx) {
                Some(true) => {}
                Some(false) => {
                    dt_cert_note(
                        mode,
                        "decline: G forall false at the injectivity-pinned point",
                    );
                    return None;
                }
                None => {
                    dt_cert_note(mode, "decline: G forall not definite under M'");
                    return None;
                }
            }
        }

        // ---- 4. Build finite tables keyed by argument e-class + collapse. ----
        // (Asserted tester/selector facts — `tester_idx`/`sel_idx` — built above —
        // drive the bounded constructor materialization used by the injectivity
        // obligation.)
        let mut tables: HashMap<String, HashMap<String, TableCertVal>> = HashMap::default();
        for name in table_syms.keys() {
            tables.insert(name.clone(), HashMap::default());
        }
        // Representative arg term per (uf, e-class) for collapse materialization.
        let mut key_reps: HashMap<String, TermId> = HashMap::default();
        // Representative per exact table row, retained for typed M' model
        // installation.  The same canonical constructor spelling may occur in
        // two distinct datatype sorts, so a global string key is insufficient
        // authority for a published function-table argument.
        let mut table_key_reps: HashMap<(String, String), TermId> = HashMap::default();
        let mut total_keys = 0usize;
        for &root in snapshot {
            let binder: Option<String> = match self.ctx.terms.get(root) {
                TermData::Forall(vars, _, _) if vars.len() == 1 => Some(vars[0].0.clone()),
                _ => None,
            };
            let mut visited: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = vec![root];
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    TermData::Let(bindings, b) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*b);
                    }
                    TermData::App(sym, args) => {
                        let name = sym.name().to_string();
                        let args = args.clone();
                        stack.extend(args.iter().copied());
                        if !table_syms.contains_key(&name) || args.len() != 1 {
                            continue;
                        }
                        let arg = args[0];
                        // Skip the certified binder application `uf(x)`.
                        if let (Some(b), TermData::Var(n, _)) =
                            (binder.as_deref(), self.ctx.terms.get(arg))
                        {
                            if n == b {
                                continue;
                            }
                        }
                        // Ground observation `uf(c)`: key by c's committed
                        // e-class, value by exact evaluation of the app.
                        let Some(key) = self.dt_cert_value_key(&model, arg) else {
                            dt_cert_note(mode, "decline: unresolvable e-class key for a table arg");
                            return None;
                        };
                        let Some(val) = self.dt_cert_scalar_val(&model, t, table_syms.get(&name)?)
                        else {
                            dt_cert_note(mode, "decline: table value not a definite scalar");
                            return None;
                        };
                        let tab = tables.get_mut(&name)?;
                        match tab.get(&key) {
                            Some(existing) if *existing != val => {
                                dt_cert_note(
                                    mode,
                                    "decline: e-class congruence conflict (one class, two values)",
                                );
                                return None;
                            }
                            Some(_) => {}
                            None => {
                                total_keys += 1;
                                if total_keys > MAX_DT_CERT_KEYS {
                                    return None;
                                }
                                tab.insert(key.clone(), val);
                            }
                        }
                        key_reps.entry(key.clone()).or_insert(arg);
                        table_key_reps.entry((name, key)).or_insert(arg);
                    }
                    _ => {}
                }
            }
        }

        // ---- 5. INJECTIVITY / distinct-collapse obligation. ----
        // Two DISTINCT e-classes that materialize to the SAME constructor
        // normal form violate datatype injectivity — DECLINE.
        {
            let mut form_owner: HashMap<String, String> = HashMap::default();
            let mut reps: Vec<(String, TermId)> =
                key_reps.iter().map(|(k, &t)| (k.clone(), t)).collect();
            reps.sort_by(|a, b| a.0.cmp(&b.0));
            for (class_key, rep) in reps {
                let Some(form) = self.dt_cert_forced_form(
                    &model,
                    rep,
                    DT_CERT_FORM_DEPTH,
                    &tester_idx,
                    &sel_idx,
                ) else {
                    continue; // abstract e-class: no forced constructor form
                };
                match form_owner.get(&form) {
                    Some(other) if *other != class_key => {
                        dt_cert_note(
                            mode,
                            "decline: distinct e-classes collapse to one constructor value (injectivity)",
                        );
                        return None;
                    }
                    _ => {
                        form_owner.insert(form, class_key);
                    }
                }
            }
        }

        // ---- 6. Default-vector enumeration + F4 cell evaluation. ----
        let mut sym_names: Vec<String> = table_syms.keys().cloned().collect();
        sym_names.sort_unstable();
        let mut cands_per_sym: Vec<Vec<TableCertVal>> = Vec::with_capacity(sym_names.len());
        for name in &sym_names {
            let codomain = *table_syms.get(name)?;
            let mut cands: Vec<TableCertVal> = Vec::new();
            match codomain {
                TableCertSort::Bool => {
                    cands.push(TableCertVal::Bool(false));
                    cands.push(TableCertVal::Bool(true));
                }
                TableCertSort::Int => {
                    let mut seen: HashSet<BigInt> = HashSet::default();
                    for v in [BigInt::ZERO, BigInt::from(1), BigInt::from(-1)] {
                        if seen.insert(v.clone()) {
                            cands.push(TableCertVal::Int(v));
                        }
                    }
                    if let Some(tab) = tables.get(name) {
                        let mut vals: Vec<BigInt> = tab
                            .values()
                            .filter_map(|v| match v {
                                TableCertVal::Int(i) => Some(i.clone()),
                                _ => None,
                            })
                            .collect();
                        vals.sort();
                        vals.dedup();
                        for v in vals.into_iter().take(2) {
                            if cands.len() >= MAX_DT_CERT_DEFAULTS_PER_SYM {
                                break;
                            }
                            if seen.insert(v.clone()) {
                                cands.push(TableCertVal::Int(v));
                            }
                        }
                    }
                }
                TableCertSort::Real => {
                    use num_rational::BigRational;
                    let mut seen: Vec<BigRational> = Vec::new();
                    for v in [
                        BigRational::from_integer(BigInt::ZERO),
                        BigRational::from_integer(BigInt::from(1)),
                        BigRational::from_integer(BigInt::from(-1)),
                    ] {
                        if !seen.contains(&v) {
                            seen.push(v.clone());
                            cands.push(TableCertVal::Rat(v));
                        }
                    }
                    if let Some(tab) = tables.get(name) {
                        let mut vals: Vec<BigRational> = tab
                            .values()
                            .filter_map(|v| match v {
                                TableCertVal::Rat(r) => Some(r.clone()),
                                _ => None,
                            })
                            .collect();
                        vals.sort();
                        vals.dedup();
                        for v in vals.into_iter().take(2) {
                            if cands.len() >= MAX_DT_CERT_DEFAULTS_PER_SYM {
                                break;
                            }
                            if !seen.contains(&v) {
                                seen.push(v.clone());
                                cands.push(TableCertVal::Rat(v));
                            }
                        }
                    }
                }
            }
            cands_per_sym.push(cands);
        }

        // Per-forall key set (union over that body's table symbols).
        let mut keys_per_forall: Vec<Vec<String>> = Vec::with_capacity(infos.len());
        for info in &infos {
            let mut keys: HashSet<String> = HashSet::default();
            for name in &info.body_syms {
                if let Some(tab) = tables.get(name) {
                    keys.extend(tab.keys().cloned());
                }
            }
            let mut keys: Vec<String> = keys.into_iter().collect();
            keys.sort_unstable();
            keys_per_forall.push(keys);
        }

        // Mixed-radix enumeration of default vectors, capped.
        let mut combo_idx: Vec<usize> = vec![0; sym_names.len()];
        let mut combo_count = 0usize;
        loop {
            combo_count += 1;
            if combo_count > MAX_DT_CERT_DEFAULT_COMBOS {
                dt_cert_note(mode, "decline: default-vector budget exhausted");
                return None;
            }
            let defaults: HashMap<String, TableCertVal> = sym_names
                .iter()
                .enumerate()
                .map(|(si, n)| (n.clone(), cands_per_sym[si][combo_idx[si]].clone()))
                .collect();

            let mut all_ok = true;
            'forall: for (fi, info) in infos.iter().enumerate() {
                // Exception leaves + JOINT DEFAULT CELL.
                let mut cells: Vec<Option<String>> = keys_per_forall[fi]
                    .iter()
                    .map(|k| Some(k.clone()))
                    .collect();
                cells.push(None); // joint default cell
                for cell in &cells {
                    match self.dt_cert_check_cell(
                        &model,
                        info.body,
                        &info.var_name,
                        &table_syms,
                        &tables,
                        &defaults,
                        cell.as_deref(),
                    ) {
                        Some(true) => {}
                        Some(false) => {
                            all_ok = false;
                            break 'forall;
                        }
                        None => {
                            dt_cert_note(mode, "decline: cell evaluation not definite");
                            return None;
                        }
                    }
                }
            }
            if all_ok {
                dt_cert_note(
                    mode,
                    &format!(
                        "certified SAT ({} DT forall(s), {} table sym(s))",
                        infos.len(),
                        sym_names.len()
                    ),
                );
                // EUF-EXTRACTION FAITHFULNESS GUARANTEE (blocking pin #5): before
                // ANY grant (shadow would-grant OR authoritative), cross-check
                // the certified tables against the solver's committed
                // per-application values. A would-grant that fails faithfulness
                // logs a would-DECLINE instead and withholds (fail-closed). This
                // is what stands between the cert's grant and a wrong-SAT via a
                // dropped/misassigned extraction row.
                if let Err(reason) = self.dt_cert_extraction_faithful(
                    &model,
                    snapshot,
                    &table_syms,
                    &tables,
                    &defaults,
                    &bridge_rewrite,
                ) {
                    dt_cert_note(
                        mode,
                        &format!("[FAITHFULNESS] would-decline (extraction infidelity): {reason}"),
                    );
                    return None;
                }
                dt_cert_note(
                    mode,
                    "[FAITHFULNESS] verified (committed values match certified cells)",
                );
                // Revalidate declaration identity/kind/signature and the
                // source scope epoch at the final authority boundary.  The
                // certificate mints and rewrites terms while checking M'; no
                // evidence captured before that work may authorize a grant if
                // the source context has since changed.
                if checked_projection_bindings
                    .iter()
                    .any(|binding| !self.ctx.projection_binding_still_current(binding))
                {
                    dt_cert_note(
                        mode,
                        "decline: datatype projection source binding became stale",
                    );
                    return None;
                }
                // F3/W1 completes a free UF with a datatype selector.  The
                // current model representation has no sealed, printable
                // selector-lambda interpretation, so publishing the incoming
                // candidate would publish M rather than the M' proved above.
                // Withhold every such grant until that interpretation can be
                // materialized exactly; structural proof alone is not model
                // authority.
                if !bridge_rewrite.is_empty() {
                    dt_cert_note(
                        mode,
                        "decline: selector-bridge completion is not representable in the published model",
                    );
                    return None;
                }
                if !matches!(mode, DtCertMode::On) {
                    return None;
                }
                // Materialize the exact F4 exception rows + default into a
                // typed total interpretation before granting.  Installation is
                // transactional and rechecks source identity/scope; failure
                // leaves the incoming model untouched and the verdict Unknown.
                self.install_dt_f4_model(
                    &table_syms,
                    &tables,
                    &defaults,
                    &table_key_reps,
                    &checked_projection_bindings,
                    &grounds,
                )?;
                return CheckedDtSatAuthority::for_current(
                    self,
                    snapshot,
                    checked_projection_bindings,
                );
            }

            // Advance mixed-radix counter.
            let mut carry = true;
            for i in (0..combo_idx.len()).rev() {
                if carry {
                    combo_idx[i] += 1;
                    if combo_idx[i] < cands_per_sym[i].len() {
                        carry = false;
                    } else {
                        combo_idx[i] = 0;
                    }
                }
            }
            if carry {
                dt_cert_note(mode, "decline: no default vector satisfies the F4 cells");
                return None;
            }
        }
    }

    /// F4 recognizer for one datatype-binder forall body: the binder `var_name`
    /// may occur ONLY as the bare direct argument of a completable UF (records
    /// the UF into `table_syms`/`body_syms`). ANY other binder occurrence — a
    /// selector/tester/constructor over `x`, a bare `x`, `uf(g(x))`,
    /// `uf(x, ..)`, an interpreted op applied to `x` directly — is out of the
    /// cell-invariant class and returns `None`. x-free subterms are left
    /// untouched (evaluated by the model evaluator). Returns `None` on any
    /// out-of-class construct.
    fn dt_cert_scan_body(
        &self,
        body: TermId,
        var_name: &str,
        xdep: &HashSet<TermId>,
        table_syms: &mut HashMap<String, TableCertSort>,
        table_requests: &mut HashMap<String, ay_frontend::ProjectionBindingRequest>,
        body_syms: &mut HashSet<String>,
    ) -> Option<()> {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            // Only x-dependent structure needs scrutiny; x-free subtrees are
            // model-pinned and handled by `evaluate_term`.
            if !xdep.contains(&t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(n, _) if n == var_name => {
                    // A bare binder not consumed by a table-UF parent: the body
                    // depends on x's IDENTITY, not just on {uf(x)} — out of the
                    // cell-invariant class.
                    return None;
                }
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // Table application `uf(x)` (bare binder trailing arg).
                    let is_binder_app = args.len() == 1
                        && matches!(self.ctx.terms.get(args[0]),
                                    TermData::Var(n, _) if n == var_name);
                    if is_binder_app {
                        // A datatype TESTER `(is-C x)` has `is_mbqi_completable_
                        // uf_symbol` true and is NOT a selector/constructor NAME,
                        // yet it is INTERPRETED (`forall x. is-Cons x` is UNSAT):
                        // it must NEVER be treated as a free finite-piecewise UF.
                        let is_tester = name
                            .strip_prefix("is-")
                            .is_some_and(|c| self.ctx.is_constructor(c).is_some());
                        if is_tester
                            || !is_mbqi_completable_uf_symbol(name)
                            || self.symbol_is_datatype_selector_or_constructor(name)
                        {
                            // Selector/tester/constructor or interpreted op on
                            // the binder: not a free finite-piecewise UF.
                            return None;
                        }
                        let codomain = match self.ctx.terms.sort(t) {
                            Sort::Bool => TableCertSort::Bool,
                            Sort::Int => TableCertSort::Int,
                            Sort::Real => TableCertSort::Real,
                            _ => return None,
                        };
                        let request = ay_frontend::ProjectionBindingRequest {
                            symbol: sym.clone(),
                            parameter_sorts: args
                                .iter()
                                .map(|&arg| self.ctx.terms.sort(arg).clone())
                                .collect(),
                            result_sort: self.ctx.terms.sort(t).clone(),
                        };
                        match table_syms.get(name) {
                            Some(&cs) if cs != codomain => return None,
                            Some(_) => {}
                            None => {
                                table_syms.insert(name.to_string(), codomain);
                            }
                        }
                        match table_requests.get(name) {
                            Some(existing) if existing != &request => return None,
                            Some(_) => {}
                            None => {
                                table_requests.insert(name.to_string(), request);
                            }
                        }
                        body_syms.insert(name.to_string());
                        // Do NOT descend into the consumed binder argument.
                        continue;
                    }
                    // Any other x-dependent application must be an interpreted
                    // arith/bool composite whose x-dependence flows only through
                    // nested table apps; descend. A UF/selector wrapping x in a
                    // non-bare shape (`uf(g(x))`, `uf(x, c)`, `sel(x)`) is out of
                    // class.
                    if is_finite_table_interpreted_symbol(name) {
                        stack.extend(args.iter().copied());
                        continue;
                    }
                    return None;
                }
                // Const cannot be x-dependent; Let/quantifiers are out of class.
                _ => return None,
            }
        }
        Some(())
    }

    /// The committed e-class identity of a datatype-sorted term `t`, used as a
    /// finite-table row key (congruent terms share it). Prefers the total-DT
    /// construction pin, then the EUF committed element, then a nullary
    /// constructor name, then a structural constructor form. `None` when the
    /// term has no committed datatype identity (fail closed).
    fn dt_cert_value_key(&self, model: &Model, t: TermId) -> Option<String> {
        if let Some(EvalValue::Element(s)) = model.dt_pins.get(&t) {
            return Some(s.clone());
        }
        if let Some(euf) = model.euf_model.as_ref() {
            if let Some(s) = euf.term_values.get(&t) {
                return Some(s.clone());
            }
        }
        if let TermData::Var(n, _) = self.ctx.terms.get(t) {
            if self.ctx.is_constructor(n).is_some_and(|(_, c)| {
                self.ctx
                    .constructor_selector_info(&c)
                    .is_none_or(|f| f.is_empty())
            }) {
                return Some(n.clone());
            }
        }
        // Last resort: a fully-ground constructor application resolves to its
        // own structural form (still a stable identity).
        self.dt_cert_structural_form(model, t, DT_CERT_FORM_DEPTH)
    }

    /// The exact scalar value of a table application under the candidate model,
    /// classified by the symbol's declared codomain. `None` on any non-definite
    /// or kind-mismatched result (fail closed).
    fn dt_cert_scalar_val(
        &self,
        model: &Model,
        app: TermId,
        codomain: &TableCertSort,
    ) -> Option<TableCertVal> {
        match (codomain, self.evaluate_term(model, app)) {
            (TableCertSort::Bool, EvalValue::Bool(b)) => Some(TableCertVal::Bool(b)),
            (TableCertSort::Int, EvalValue::Rational(r)) if r.is_integer() => {
                Some(TableCertVal::Int(r.numer().clone()))
            }
            (TableCertSort::Real, EvalValue::Rational(r)) => Some(TableCertVal::Rat(r)),
            _ => None,
        }
    }

    /// Index the ASSERTED top-level ground facts that drive bounded constructor
    /// materialization: `(is-C t)` testers (forced constructor) and
    /// `(= (sel t) v)` / `(= v (sel t))` selector equalities. Both are true in
    /// every model, so reading them is sound.
    #[allow(clippy::type_complexity)]
    fn dt_cert_index_ground_facts(
        &self,
        grounds: &[TermId],
    ) -> (HashMap<TermId, String>, HashMap<(String, TermId), TermId>) {
        let mut tester_idx: HashMap<TermId, String> = HashMap::default();
        let mut sel_idx: HashMap<(String, TermId), TermId> = HashMap::default();
        let is_selector = |name: &str| {
            self.ctx
                .ctor_selectors_iter()
                .any(|(_c, sels)| sels.iter().any(|s| s == name))
        };
        for &g in grounds {
            if let TermData::App(sym, args) = self.ctx.terms.get(g) {
                let name = sym.name();
                if let Some(ctor) = name.strip_prefix("is-") {
                    if args.len() == 1 && self.ctx.is_constructor(ctor).is_some() {
                        tester_idx
                            .entry(args[0])
                            .or_insert_with(|| ctor.to_string());
                    }
                }
                if name == "=" && args.len() == 2 {
                    for (sel_side, val_side) in [(args[0], args[1]), (args[1], args[0])] {
                        if let TermData::App(ssym, sargs) = self.ctx.terms.get(sel_side) {
                            if sargs.len() == 1 && is_selector(ssym.name()) {
                                sel_idx
                                    .entry((ssym.name().to_string(), sargs[0]))
                                    .or_insert(val_side);
                            }
                        }
                    }
                }
            }
        }
        (tester_idx, sel_idx)
    }

    /// Structural constructor normal form of a term that is (transitively) a
    /// constructor application, as a canonical string; `None` for any abstract
    /// / non-constructor term.
    fn dt_cert_structural_form(&self, model: &Model, t: TermId, depth: u32) -> Option<String> {
        if depth == 0 {
            return None;
        }
        match self.ctx.terms.get(t).clone() {
            TermData::Var(n, _) => {
                let (_, ctor) = self.ctx.is_constructor(&n)?;
                if self
                    .ctx
                    .constructor_selector_info(&ctor)
                    .is_none_or(|f| f.is_empty())
                {
                    Some(ctor)
                } else {
                    None
                }
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                let (_, ctor) = self.ctx.is_constructor(name)?;
                self.dt_cert_form_from_fields(model, &ctor, &args, depth)
            }
            _ => None,
        }
    }

    /// The constructor normal form of the e-class of `t` — from a constructor
    /// application, else from an ASSERTED tester + selector facts. Enforces the
    /// injectivity obligation: two distinct e-classes with the same result form
    /// collapse. `None` for an unforced (abstract) e-class.
    fn dt_cert_forced_form(
        &self,
        model: &Model,
        t: TermId,
        depth: u32,
        tester_idx: &HashMap<TermId, String>,
        sel_idx: &HashMap<(String, TermId), TermId>,
    ) -> Option<String> {
        if depth == 0 {
            return None;
        }
        // Direct constructor application.
        if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
            if let Some((_, ctor)) = self.ctx.is_constructor(sym.name()) {
                return self.dt_cert_form_from_fields(model, &ctor, &args, depth);
            }
        }
        if let TermData::Var(n, _) = self.ctx.terms.get(t).clone() {
            if let Some((_, ctor)) = self.ctx.is_constructor(&n) {
                if self
                    .ctx
                    .constructor_selector_info(&ctor)
                    .is_none_or(|f| f.is_empty())
                {
                    return Some(ctor);
                }
            }
        }
        // Forced by an asserted tester + selector facts.
        let ctor = tester_idx.get(&t)?;
        let selectors = self.ctx.constructor_selectors(ctor)?.to_vec();
        let fields = self.ctx.constructor_selector_info(ctor)?.to_vec();
        let mut parts: Vec<String> = Vec::with_capacity(fields.len());
        for (sel, (_, fsort)) in selectors.iter().zip(fields.iter()) {
            let v = *sel_idx.get(&(sel.clone(), t))?;
            parts.push(self.dt_cert_field_form(model, v, fsort, depth, tester_idx, sel_idx)?);
        }
        Some(format!("{ctor}({})", parts.join(",")))
    }

    /// Build a constructor form from a constructor application's positional
    /// argument terms.
    fn dt_cert_form_from_fields(
        &self,
        model: &Model,
        ctor: &str,
        args: &[TermId],
        depth: u32,
    ) -> Option<String> {
        let fields = self.ctx.constructor_selector_info(ctor)?.to_vec();
        if fields.len() != args.len() {
            return None;
        }
        if fields.is_empty() {
            return Some(ctor.to_string());
        }
        let mut parts: Vec<String> = Vec::with_capacity(args.len());
        for (&arg, (_, fsort)) in args.iter().zip(fields.iter()) {
            // No tester/selector index available on this path (structural
            // recursion), so an abstract datatype field fails closed.
            parts.push(self.dt_cert_field_form(
                model,
                arg,
                fsort,
                depth,
                &HashMap::default(),
                &HashMap::default(),
            )?);
        }
        Some(format!("{ctor}({})", parts.join(",")))
    }

    /// One field of a constructor form: recurse for a datatype field, or the
    /// committed scalar atom otherwise.
    fn dt_cert_field_form(
        &self,
        model: &Model,
        v: TermId,
        fsort: &Sort,
        depth: u32,
        tester_idx: &HashMap<TermId, String>,
        sel_idx: &HashMap<(String, TermId), TermId>,
    ) -> Option<String> {
        if self.dt_cert_sort_name(fsort).is_some() {
            self.dt_cert_forced_form(model, v, depth - 1, tester_idx, sel_idx)
        } else {
            self.dt_cert_scalar_atom(&self.evaluate_term(model, v))
        }
    }

    /// M5 (net-negative re-sequencing fix, item 5a): census-informed precheck.
    /// Does EVERY top-level `forall` in `snapshot` at least STRUCTURALLY match a
    /// cert route — F2/F3/G, or a single-`Datatype`-binder F4 candidate? Used to
    /// decline the resequence probe BEFORE its expensive ground-core solve when a
    /// `forall` is definitely unclaimable (multi-binder not F2/G, single
    /// non-datatype binder not F2/F3/G, or `no_mbqi`).
    ///
    /// Model-free and DECLINE-ONLY: the certificate grants only when EVERY
    /// `forall` is claimable (all-or-nothing), so a `false` here can only turn a
    /// certain decline into a cheaper one — it never suppresses a grant. The F4
    /// leg is over-approximated (single datatype binder, no cell-invariance
    /// check), which is safe: a body the full F4 scan later rejects merely
    /// proceeds to the solve exactly as today.
    pub(in crate::executor) fn dt_cert_snapshot_structurally_claimable(
        &self,
        snapshot: &[TermId],
    ) -> bool {
        // W1 bridge-route precheck leg (`AY_DT_CERT_BRIDGE_ROUTE`): the
        // snapshot's F3 selector-bridge pins, collected lazily — ONLY when a
        // forall fails every existing route while the route flag is on, so the
        // flag-off path is byte-identical. `None` = not yet collected.
        let mut bridge_pins: Option<HashMap<String, String>> = None;
        for &a in snapshot {
            let (vars, body) = match self.ctx.terms.get(a) {
                TermData::Forall(vars, body, _) => (vars.clone(), *body),
                _ => continue,
            };
            if self.ctx.terms.is_no_mbqi(a) {
                return false;
            }
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            let claimable = self.dt_cert_classify_f2(&var_names, body).is_some()
                || self.dt_cert_classify_f3(&var_names, body).is_some()
                || self.dt_cert_classify_g(&var_names, body).is_some()
                || (vars.len() == 1 && self.dt_cert_sort_name(&vars[0].1).is_some());
            if !claimable {
                // W1 leg: a bridge-UF-over-constructor tautology is claimable
                // iff its selector-bridge premise (an F3 pin to EXACTLY the
                // constructor's field-idx selector) is ALSO in the snapshot —
                // the same mandatory gate the full certificate applies, so
                // this leg is EXACT for W1 (no over-approximation) and
                // decline-only (it can never suppress a grant).
                if !dt_cert_bridge_route_enabled() {
                    return false;
                }
                let Some((bridge, ctor, idx)) = self.dt_cert_classify_f2_bridge(&var_names, body)
                else {
                    return false;
                };
                let pins =
                    bridge_pins.get_or_insert_with(|| self.dt_cert_collect_f3_pins(snapshot));
                let Some(pinned_sel) = pins.get(&bridge) else {
                    return false;
                };
                let Some(selectors) = self.ctx.constructor_selectors(&ctor) else {
                    return false;
                };
                if selectors.get(idx) != Some(pinned_sel) {
                    return false;
                }
            }
        }
        true
    }

    /// The snapshot's F3 selector-bridge pins (bridge-UF name → pinned
    /// declared-selector name), for the precheck's W1 bridge-route leg.
    /// First-pin-wins on a doubly-pinned bridge — an over-approximation the
    /// full certificate declines ("bridge UF mapped to two selectors"), which
    /// is safe because the precheck is decline-only.
    fn dt_cert_collect_f3_pins(&self, snapshot: &[TermId]) -> HashMap<String, String> {
        let mut pins: HashMap<String, String> = HashMap::default();
        for &a in snapshot {
            let (vars, body) = match self.ctx.terms.get(a) {
                TermData::Forall(vars, body, _) => (vars.clone(), *body),
                _ => continue,
            };
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            if let Some((bridge, sel)) = self.dt_cert_classify_f3(&var_names, body) {
                pins.entry(bridge).or_insert(sel);
            }
        }
        pins
    }

    /// Datatype sort name of `sort` (either a `Sort::Datatype` or a
    /// `Sort::Uninterpreted` registered as a declared datatype). Local to the
    /// certificate to avoid the private model-module helper.
    fn dt_cert_sort_name(&self, sort: &Sort) -> Option<String> {
        match sort {
            Sort::Datatype(dt) => Some(dt.name.clone()),
            Sort::Uninterpreted(name) => self
                .ctx
                .datatype_iter()
                .any(|(n, _)| n == name)
                .then(|| name.clone()),
            _ => None,
        }
    }

    /// Canonical scalar atom string of a committed value (constructor-field
    /// rendering for the injectivity form). `None` on a non-definite value.
    fn dt_cert_scalar_atom(&self, ev: &EvalValue) -> Option<String> {
        match ev {
            EvalValue::Bool(b) => Some(b.to_string()),
            EvalValue::Element(e) => Some(e.clone()),
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Some(r.numer().to_string())
                } else {
                    Some(format!("(/ {} {})", r.numer(), r.denom()))
                }
            }
            EvalValue::String(s) => Some(s.clone()),
            EvalValue::BitVec { value, width } => Some(format!("bv{value}_{width}")),
            _ => None,
        }
    }

    /// Tri-state cardinality classifier for the binder datatype: `Some` when it
    /// is recursive / has an infinite scalar field (⇒ infinite domain) OR all
    /// constructors are nullary (⇒ finite/exhaustive); `None` (DECLINE) for a
    /// datatype this M1 cannot soundly classify.
    fn dt_cert_cardinality(&self, dt_name: &str) -> Option<()> {
        let ctors: Vec<String> = self
            .ctx
            .datatype_iter()
            .find(|(n, _)| *n == dt_name)
            .map(|(_, cs)| cs.to_vec())?;
        if ctors.is_empty() {
            return None;
        }
        let mut all_nullary = true;
        let mut infinite = false;
        for c in &ctors {
            let fields = self.ctx.constructor_selector_info(c)?;
            if !fields.is_empty() {
                all_nullary = false;
            }
            for (_, fs) in fields {
                match fs {
                    Sort::Int | Sort::Real | Sort::String | Sort::Seq(_) => infinite = true,
                    _ if self.dt_cert_sort_name(fs).is_some() => infinite = true,
                    _ => {}
                }
            }
        }
        if infinite || all_nullary {
            Some(())
        } else {
            None
        }
    }

    /// Evaluate a certified body at ONE cell of the completed model `M'`:
    /// substitute every binder application `uf(x)` by its cell value (the table
    /// row for `Some(key)`, else / for the joint default cell `None`, the
    /// symbol's chosen default), producing an x-FREE ground term, then evaluate
    /// it under `M`. `Some(true/false)` = the cell holds / fails; `None` = a
    /// hard decline (binder leaked past cell-invariance, or a value/eval was not
    /// definite).
    #[allow(clippy::too_many_arguments)]
    fn dt_cert_check_cell(
        &mut self,
        model: &Model,
        body: TermId,
        var_name: &str,
        table_syms: &HashMap<String, TableCertSort>,
        tables: &HashMap<String, HashMap<String, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        cell: Option<&str>,
    ) -> Option<bool> {
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let ground = self.dt_cert_subst_cell(
            body, var_name, table_syms, tables, defaults, cell, &mut memo,
        )?;
        if self.finite_table_mentions_var(ground, var_name) {
            return None; // cell-invariance breach — fail closed
        }
        match self.evaluate_term(model, ground) {
            EvalValue::Bool(true) => Some(true),
            EvalValue::Bool(false) => Some(false),
            _ => None,
        }
    }

    /// Substitute every binder application `uf(x)` in `body` by the constant of
    /// its cell value; rebuild the surrounding structure verbatim. `None` on a
    /// bare binder outside a table app (cell-invariance breach) or a missing
    /// cell value.
    #[allow(clippy::too_many_arguments)]
    fn dt_cert_subst_cell(
        &mut self,
        t: TermId,
        var_name: &str,
        table_syms: &HashMap<String, TableCertSort>,
        tables: &HashMap<String, HashMap<String, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        cell: Option<&str>,
        memo: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        if let Some(&r) = memo.get(&t) {
            return Some(r);
        }
        let result = match self.ctx.terms.get(t).clone() {
            TermData::Var(ref n, _) if n == var_name => return None,
            TermData::Not(i) => {
                let ri =
                    self.dt_cert_subst_cell(i, var_name, table_syms, tables, defaults, cell, memo)?;
                self.ctx.terms.mk_not(ri)
            }
            TermData::Ite(c, a, b) => {
                let rc =
                    self.dt_cert_subst_cell(c, var_name, table_syms, tables, defaults, cell, memo)?;
                let ra =
                    self.dt_cert_subst_cell(a, var_name, table_syms, tables, defaults, cell, memo)?;
                let rb =
                    self.dt_cert_subst_cell(b, var_name, table_syms, tables, defaults, cell, memo)?;
                self.ctx.terms.mk_ite(rc, ra, rb)
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                let is_binder_app = args.len() == 1
                    && table_syms.contains_key(name)
                    && matches!(self.ctx.terms.get(args[0]),
                                TermData::Var(n, _) if n == var_name);
                if is_binder_app {
                    let v = match cell {
                        Some(key) => tables
                            .get(name)
                            .and_then(|tab| tab.get(key))
                            .cloned()
                            .or_else(|| defaults.get(name).cloned()),
                        None => defaults.get(name).cloned(),
                    }?;
                    match v {
                        TableCertVal::Int(i) => self.ctx.terms.mk_int(i),
                        TableCertVal::Rat(r) => self.ctx.terms.mk_rational(r),
                        TableCertVal::Bool(b) => self.ctx.terms.mk_bool(b),
                    }
                } else {
                    let mut new_args: Vec<TermId> = Vec::with_capacity(args.len());
                    for a in &args {
                        new_args.push(self.dt_cert_subst_cell(
                            *a, var_name, table_syms, tables, defaults, cell, memo,
                        )?);
                    }
                    let sort = self.ctx.terms.sort(t).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            // Const, x-free var, or anything else: verbatim (x-free by the
            // scan; only the binder-application subterms carry x).
            _ => t,
        };
        memo.insert(t, result);
        Some(result)
    }

    // ===================================================================
    // M4 DT-MBQI-Sat routes: G (ground-reduction), F2 (selector tautology),
    // F3 (bridge symbolic default). All grant-only, fail-closed, and — after
    // the F3 rewrite — discharged against a single completed model M'.
    // ===================================================================

    /// `body` is a binary equality `(= a b)`? Returns `(a, b)`.
    fn dt_cert_match_eq(&self, body: TermId) -> Option<(TermId, TermId)> {
        if let TermData::App(sym, args) = self.ctx.terms.get(body) {
            if sym.name() == "=" && args.len() == 2 {
                return Some((args[0], args[1]));
            }
        }
        None
    }

    /// `body` is a disjunction `(or d0 d1 ..)`? Returns the disjuncts.
    fn dt_cert_match_or(&self, body: TermId) -> Option<Vec<TermId>> {
        if let TermData::App(sym, args) = self.ctx.terms.get(body) {
            if sym.name() == "or" && args.len() >= 2 {
                return Some(args.clone());
            }
        }
        None
    }

    /// `args` are EXACTLY the bound variables `var_names` in declaration order
    /// (each a distinct bare binder). This is the datatype injectivity anchor:
    /// `t = C(v0..vk)` pins `(v0..vk)` uniquely to `(sel_0 t .. sel_k t)`.
    fn dt_cert_args_are_binders(&self, args: &[TermId], var_names: &[String]) -> bool {
        if args.len() != var_names.len() {
            return false;
        }
        args.iter()
            .zip(var_names.iter())
            .all(|(&a, vn)| matches!(self.ctx.terms.get(a), TermData::Var(n, _) if n == vn))
    }

    /// `t` mentions NONE of the bound variables in `var_names` (binder-free =
    /// ground w.r.t. this forall). Fail-closed on any structural surprise.
    fn dt_cert_binder_free(&self, t: TermId, var_names: &[String]) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![t];
        while let Some(u) = stack.pop() {
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Var(n, _) => {
                    if var_names.iter().any(|vn| vn == n) {
                        return false;
                    }
                }
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Const(_) => {}
                // Nested binders / lets are out of the ground-reduction class.
                _ => return false,
            }
        }
        true
    }

    /// `t` transitively mentions an application of any F3 bridge UF.
    fn dt_cert_term_mentions_bridge(
        &self,
        t: TermId,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
    ) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![t];
        while let Some(u) = stack.pop() {
            if !visited.insert(u) {
                continue;
            }
            match self.ctx.terms.get(u) {
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    if bridge_rewrite.contains_key(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                _ => {}
            }
        }
        false
    }

    /// Declared field sort of a datatype selector `sel_name` (its codomain).
    fn dt_cert_selector_field_sort(&self, sel_name: &str) -> Option<Sort> {
        for (ctor, sels) in self.ctx.ctor_selectors_iter() {
            if let Some(idx) = sels.iter().position(|s| s == sel_name) {
                let info = self.ctx.constructor_selector_info(ctor)?;
                return info.get(idx).map(|(_, s)| s.clone());
            }
        }
        None
    }

    /// F2 recognizer — DT-selector tautology `sel_i(C(v0..vk)) = v_i` (either
    /// equality orientation), where `sel_i` IS `C`'s declared selector for field
    /// `i` (verified against the datatype declaration, not by name-string) and
    /// `v_i` is exactly the i-th binder. Model-independent theory tautology.
    fn dt_cert_classify_f2(&self, var_names: &[String], body: TermId) -> Option<()> {
        let (a, b) = self.dt_cert_match_eq(body)?;
        for (sel_side, var_side) in [(a, b), (b, a)] {
            let TermData::App(ssym, sargs) = self.ctx.terms.get(sel_side) else {
                continue;
            };
            if sargs.len() != 1 {
                continue;
            }
            let sel_name = ssym.name().to_string();
            let cons_app = sargs[0];
            let TermData::App(csym, cargs) = self.ctx.terms.get(cons_app) else {
                continue;
            };
            let cargs = cargs.clone();
            let Some((_, ctor)) = self.ctx.is_constructor(csym.name()) else {
                continue;
            };
            if !self.dt_cert_args_are_binders(&cargs, var_names) {
                continue;
            }
            let selectors = self.ctx.constructor_selectors(&ctor)?.to_vec();
            let Some(idx) = selectors.iter().position(|s| *s == sel_name) else {
                continue;
            };
            // The equated side must be exactly the i-th field binder.
            if idx < var_names.len()
                && matches!(self.ctx.terms.get(var_side),
                            TermData::Var(n, _) if *n == var_names[idx])
            {
                return Some(());
            }
        }
        None
    }

    /// W1 (bridge-route) recognizer — bridge-UF-over-constructor tautology
    /// `bridge(C(v0..vk)) = v_i` (either equality orientation), where `bridge`
    /// is a FREE completable UF (NOT a declared selector/constructor/tester —
    /// those are F2's), applied to a constructor over EXACTLY the binders in
    /// declaration order, and the equated side is the bare `i`-th binder.
    /// Returns `(bridge_name, ctor_name, i)`.
    ///
    /// STRUCTURAL ONLY — this match alone is NOT sound (over a genuinely free
    /// UF the body is an unverified constraint, not a tautology). The claim is
    /// certified solely by COMPOSITION with an in-snapshot F3 selector-bridge
    /// pin `is-C(x) => bridge(x) = sel_i(x)`: under the completed model M'
    /// (which interprets `bridge` AS the pinned selector) the body rewrites to
    /// the native selector tautology `sel_i(C(v0..vk)) = v_i`. The MANDATORY
    /// premise gate in `try_dt_model_sat_certificate` (step 2c) declines any
    /// claim whose bridge is unpinned or pinned to a different selector.
    fn dt_cert_classify_f2_bridge(
        &self,
        var_names: &[String],
        body: TermId,
    ) -> Option<(String, String, usize)> {
        let (a, b) = self.dt_cert_match_eq(body)?;
        for (uf_side, var_side) in [(a, b), (b, a)] {
            let TermData::App(usym, uargs) = self.ctx.terms.get(uf_side) else {
                continue;
            };
            if uargs.len() != 1 {
                continue;
            }
            let bridge_name = usym.name().to_string();
            let cons_app = uargs[0];
            // The head must be a FREE completable UF — not a declared
            // selector/constructor (F2's territory) and not a tester.
            if !is_mbqi_completable_uf_symbol(&bridge_name)
                || self.symbol_is_datatype_selector_or_constructor(&bridge_name)
                || bridge_name
                    .strip_prefix("is-")
                    .is_some_and(|c| self.ctx.is_constructor(c).is_some())
            {
                continue;
            }
            let TermData::App(csym, cargs) = self.ctx.terms.get(cons_app) else {
                continue;
            };
            let cargs = cargs.clone();
            let Some((_, ctor)) = self.ctx.is_constructor(csym.name()) else {
                continue;
            };
            if !self.dt_cert_args_are_binders(&cargs, var_names) {
                continue;
            }
            // The equated side must be exactly ONE bare binder; its position
            // in the binder list is the claimed field index.
            if let TermData::Var(n, _) = self.ctx.terms.get(var_side) {
                if let Some(idx) = var_names.iter().position(|vn| vn == n) {
                    return Some((bridge_name, ctor, idx));
                }
            }
        }
        None
    }

    /// The W1 MANDATORY selector-bridge-premise gate for ONE structural claim
    /// `(bridge, ctor, idx)`: certified iff `bridge` is F3-pinned
    /// (`bridge_rewrite`) and the pinned selector IS `ctor`'s declared
    /// field-`idx` selector — then, under the completed M' (bridge ≡ pinned
    /// selector), the claimed body is exactly the native F2 selector
    /// tautology. `Ok(pinned selector)` on pass; `Err(decline reason)`
    /// fail-closed otherwise (unpinned = genuinely free bridge, or a pin to a
    /// different selector — either claim would be a wrong-grant).
    fn dt_cert_bridge_claim_check(
        &self,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
        bridge: &str,
        ctor: &str,
        idx: usize,
    ) -> std::result::Result<String, String> {
        let Some((pinned_sel, _)) = bridge_rewrite.get(bridge) else {
            return Err(format!(
                "bridge UF `{bridge}` has no in-snapshot selector-bridge pin (genuinely free \
                 bridge)"
            ));
        };
        let Some(selectors) = self.ctx.constructor_selectors(ctor) else {
            return Err(format!("constructor `{ctor}` has no declared selectors"));
        };
        if selectors.get(idx) != Some(pinned_sel) {
            return Err(format!(
                "bridge UF `{bridge}` is pinned to `{pinned_sel}`, not `{ctor}`'s field-{idx} \
                 selector"
            ));
        }
        Ok(pinned_sel.clone())
    }

    /// F3 recognizer — bridge symbolic-default closure
    /// `(or (= (bridge x) (sel_i x)) (not (is-C x)))` (single binder `x`), where
    /// `bridge` is a free completable UF, `sel_i` is `C`'s declared selector, and
    /// `is-C` is `C`'s tester. Returns `(bridge_name, sel_name)`.
    fn dt_cert_classify_f3(&self, var_names: &[String], body: TermId) -> Option<(String, String)> {
        if var_names.len() != 1 {
            return None;
        }
        let x = &var_names[0];
        let disjuncts = self.dt_cert_match_or(body)?;
        if disjuncts.len() != 2 {
            return None;
        }
        let mut eq_disj: Option<TermId> = None;
        let mut guard_ok = false;
        for &d in &disjuncts {
            if let TermData::Not(inner) = self.ctx.terms.get(d) {
                if let TermData::App(sym, sargs) = self.ctx.terms.get(*inner) {
                    if sargs.len() == 1 {
                        if let Some(ctor) = sym.name().strip_prefix("is-") {
                            if self.ctx.is_constructor(ctor).is_some()
                                && matches!(self.ctx.terms.get(sargs[0]),
                                            TermData::Var(n, _) if n == x)
                            {
                                guard_ok = true;
                                continue;
                            }
                        }
                    }
                }
            }
            eq_disj = Some(d);
        }
        if !guard_ok {
            return None;
        }
        let (a, b) = self.dt_cert_match_eq(eq_disj?)?;
        for (bside, sside) in [(a, b), (b, a)] {
            let Some(bname) = self.dt_cert_unary_binder_app(bside, x) else {
                continue;
            };
            let Some(sname) = self.dt_cert_unary_binder_app(sside, x) else {
                continue;
            };
            // `sside` must be a DECLARED selector; `bside` a free completable UF
            // that is NOT itself a selector/constructor/tester.
            let s_is_selector = self
                .ctx
                .ctor_selectors_iter()
                .any(|(_c, sels)| sels.iter().any(|s| *s == sname));
            let b_is_free = is_mbqi_completable_uf_symbol(&bname)
                && !self.symbol_is_datatype_selector_or_constructor(&bname)
                && bname
                    .strip_prefix("is-")
                    .is_none_or(|c| self.ctx.is_constructor(c).is_none());
            if s_is_selector && b_is_free {
                return Some((bname, sname));
            }
        }
        None
    }

    /// `t = App(name, [Var(x)])` — a unary application of `name` on the bare
    /// binder `x`. Returns `name`.
    fn dt_cert_unary_binder_app(&self, t: TermId, x: &str) -> Option<String> {
        if let TermData::App(sym, args) = self.ctx.terms.get(t) {
            if args.len() == 1
                && matches!(self.ctx.terms.get(args[0]), TermData::Var(n, _) if n == x)
            {
                return Some(sym.name().to_string());
            }
        }
        None
    }

    /// Recover the exact core head and complete application signature for a
    /// name nominated by the F3/W1 structural recognizers.  This does not
    /// classify the declaration: the returned request remains untrusted until
    /// [`Self::check_table_declaration_occurrences`] positively binds it to one
    /// live ordinary free-UF declaration and checks every occurrence.
    fn dt_cert_projection_request(
        &self,
        root: TermId,
        name: &str,
    ) -> Option<ay_frontend::ProjectionBindingRequest> {
        const MAX_DT_PROJECTION_REQUEST_TERMS: usize = 100_000;

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if term.index() >= self.ctx.terms.len() {
                return None;
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_DT_PROJECTION_REQUEST_TERMS {
                return None;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) => {
                    if symbol.name() == name {
                        return Some(ay_frontend::ProjectionBindingRequest {
                            symbol: symbol.clone(),
                            parameter_sorts: args
                                .iter()
                                .map(|&arg| self.ctx.terms.sort(arg).clone())
                                .collect(),
                            result_sort: self.ctx.terms.sort(term).clone(),
                        });
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => return None,
            }
        }
        None
    }

    /// G recognizer — ground-reduction `forall v0..vk. (or phi (not (= t
    /// C(v0..vk))))`, where `t` is GROUND (binder-free), `C` is a constructor
    /// whose arity equals the binder count, and its application uses exactly the
    /// binders in order. DT injectivity pins `(v0..vk)` uniquely at `(sel_i t)`,
    /// so `phi` at that single point decides the whole universal.
    fn dt_cert_classify_g(&self, var_names: &[String], body: TermId) -> Option<GCertInfo> {
        let disjuncts = self.dt_cert_match_or(body)?;
        let mut guard_idx: Option<usize> = None;
        let mut t_ground: Option<TermId> = None;
        let mut ctor_name: Option<String> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            let TermData::Not(inner) = self.ctx.terms.get(d) else {
                continue;
            };
            let Some((eq_a, eq_b)) = self.dt_cert_match_eq(*inner) else {
                continue;
            };
            for (cside, tside) in [(eq_a, eq_b), (eq_b, eq_a)] {
                let TermData::App(csym, cargs) = self.ctx.terms.get(cside) else {
                    continue;
                };
                let cargs = cargs.clone();
                let Some((_, ctor)) = self.ctx.is_constructor(csym.name()) else {
                    continue;
                };
                // C's application must be over exactly the binders, and the
                // other side `t` must be ground (binder-free).
                if self.dt_cert_args_are_binders(&cargs, var_names)
                    && self.dt_cert_binder_free(tside, var_names)
                {
                    guard_idx = Some(i);
                    t_ground = Some(tside);
                    ctor_name = Some(ctor);
                    break;
                }
            }
            if guard_idx.is_some() {
                break;
            }
        }
        let gi = guard_idx?;
        // phi = the (single) other disjunct. A phi split across several
        // disjuncts would need a fresh `or` (mint); decline (conservative).
        let others: Vec<TermId> = disjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != gi)
            .map(|(_, &d)| d)
            .collect();
        if others.len() != 1 {
            return None;
        }
        Some(GCertInfo {
            t: t_ground?,
            ctor: ctor_name?,
            phi: others[0],
            var_names: var_names.to_vec(),
        })
    }

    /// The completed-model constructor identity of `t`: `Some(true)` iff `t` is
    /// definitely constructed by `ctor` under M', `Some(false)` iff definitely by
    /// a DIFFERENT constructor, `None` (DECLINE) when indeterminate. Prefers a
    /// definite tester evaluation, then the asserted-fact forced form.
    fn dt_cert_tester_value(
        &mut self,
        model: &Model,
        t: TermId,
        ctor: &str,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
        tester_idx: &HashMap<TermId, String>,
        sel_idx: &HashMap<(String, TermId), TermId>,
    ) -> Option<bool> {
        // 1. Definite tester evaluation `(is-ctor t)` under M'.
        let tester = self
            .ctx
            .terms
            .mk_app(Symbol::named(format!("is-{ctor}")), [t], Sort::Bool);
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let tester_rw = self.dt_cert_bridge_rewrite(tester, bridge_rewrite, &mut memo);
        if let EvalValue::Bool(b) = self.evaluate_term(model, tester_rw) {
            return Some(b);
        }
        // 2. Forced constructor normal form from constructor apps / asserted
        //    tester+selector facts: read its top constructor.
        let form = self.dt_cert_forced_form(model, t, DT_CERT_FORM_DEPTH, tester_idx, sel_idx)?;
        let top = form.split('(').next().unwrap_or(&form);
        Some(top == ctor)
    }

    /// Verify one G-route forall against the completed model M'. `Some(true)` =
    /// certified (vacuous, or `phi` holds at the injectivity-pinned point);
    /// `Some(false)` = `phi` FALSE at the pinned point (DECLINE, never sat);
    /// `None` = indeterminate (DECLINE).
    fn dt_cert_verify_g(
        &mut self,
        model: &Model,
        gi: &GCertInfo,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
        tester_idx: &HashMap<TermId, String>,
        sel_idx: &HashMap<(String, TermId), TermId>,
    ) -> Option<bool> {
        let selectors = self.ctx.constructor_selectors(&gi.ctor)?.to_vec();
        let field_sorts: Vec<Sort> = self
            .ctx
            .constructor_selector_info(&gi.ctor)?
            .iter()
            .map(|(_, s)| s.clone())
            .collect();
        // The guard's constructor arity must match the binder count.
        if selectors.len() != gi.var_names.len() || field_sorts.len() != selectors.len() {
            return None;
        }
        // Is `t` a `ctor` under M'?
        if !self.dt_cert_tester_value(model, gi.t, &gi.ctor, bridge_rewrite, tester_idx, sel_idx)? {
            return Some(true); // guard false for all binders — vacuous
        }
        // Pin each binder v_i := (sel_i t) (declared selector on the ground t).
        let mut subst: HashMap<String, TermId> = HashMap::default();
        for (i, vn) in gi.var_names.iter().enumerate() {
            let sel_app = self.ctx.terms.mk_app(
                Symbol::named(selectors[i].as_str()),
                [gi.t],
                field_sorts[i].clone(),
            );
            subst.insert(vn.clone(), sel_app);
        }
        let phi_sub = subst_vars(&mut self.ctx.terms, gi.phi, &subst);
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let phi_rw = self.dt_cert_bridge_rewrite(phi_sub, bridge_rewrite, &mut memo);
        // The pinned `phi` must be ground (binder-free) for a definite eval.
        if !self.dt_cert_binder_free(phi_rw, &gi.var_names) {
            return None;
        }
        match self.evaluate_term(model, phi_rw) {
            EvalValue::Bool(b) => Some(b),
            _ => None,
        }
    }

    /// W2 (bridge route) — cert-local three-valued (Kleene) evaluation of a
    /// ground assertion's BOOLEAN SKELETON under the completed model M'.
    ///
    /// `evaluate_term`'s `or`/`and` loops return `Unknown` on the FIRST
    /// non-definite operand without scanning the rest, so a guarded ground like
    /// `(or (= (sel_j (sel_k t)) …) (not (is-C (sel_k t))))` — where the inner
    /// selector lands on a NON-MATCHING constructor (SMT-LIB leaves that value
    /// underspecified ⇒ `Unknown`) but the guard disjunct is definitely true —
    /// reads `Unknown` even though the assertion is definitely true in EVERY
    /// completion of M'. Kleene semantics are strictly sound and complete-safe:
    /// `or` is true iff SOME operand is true, false iff ALL are false;
    /// `and` dually; `not`/`=>`/Bool-`ite` lifted pointwise; every leaf
    /// delegates to `evaluate_term` and stays fail-closed (`None`) unless
    /// definite. This only RECOVERS definite verdicts the two-valued scan
    /// abandoned — it can never manufacture one, because a `Some(b)` here is
    /// witnessed by definite leaf evaluations under the same single M'.
    ///
    /// Used ONLY by the certificate's ground re-verification, gated on an
    /// active bridge-route claim (`bridge_route_used`) — i.e. exclusively on
    /// the shadow-withheld path in this increment.
    fn dt_cert_eval_ground_kleene(&self, model: &Model, t: TermId) -> Option<bool> {
        match self.ctx.terms.get(t).clone() {
            TermData::Not(i) => self.dt_cert_eval_ground_kleene(model, i).map(|b| !b),
            TermData::Ite(c, a, b) => {
                // Bool-sorted ite only (scalar ites are leaves for the leaf
                // evaluator below — reached only via `=`/atoms, which
                // `evaluate_term` owns).
                match self.dt_cert_eval_ground_kleene(model, c) {
                    Some(true) => self.dt_cert_eval_ground_kleene(model, a),
                    Some(false) => self.dt_cert_eval_ground_kleene(model, b),
                    None => {
                        // Condition indefinite: definite only if BOTH branches
                        // agree definitely.
                        let va = self.dt_cert_eval_ground_kleene(model, a)?;
                        let vb = self.dt_cert_eval_ground_kleene(model, b)?;
                        (va == vb).then_some(va)
                    }
                }
            }
            TermData::App(sym, args) => match sym.name() {
                "or" => {
                    let mut all_false = true;
                    for &a in &args {
                        match self.dt_cert_eval_ground_kleene(model, a) {
                            Some(true) => return Some(true),
                            Some(false) => {}
                            None => all_false = false,
                        }
                    }
                    all_false.then_some(false)
                }
                "and" => {
                    let mut all_true = true;
                    for &a in &args {
                        match self.dt_cert_eval_ground_kleene(model, a) {
                            Some(false) => return Some(false),
                            Some(true) => {}
                            None => all_true = false,
                        }
                    }
                    all_true.then_some(true)
                }
                "not" if args.len() == 1 => {
                    self.dt_cert_eval_ground_kleene(model, args[0]).map(|b| !b)
                }
                "=>" if args.len() == 2 => {
                    match (
                        self.dt_cert_eval_ground_kleene(model, args[0]),
                        self.dt_cert_eval_ground_kleene(model, args[1]),
                    ) {
                        (Some(false), _) | (_, Some(true)) => Some(true),
                        (Some(true), Some(false)) => Some(false),
                        _ => None,
                    }
                }
                // Leaf atom (equality, tester, arithmetic relation, …):
                // delegate to the single-authority evaluator, fail-closed.
                _ => match self.evaluate_term(model, t) {
                    EvalValue::Bool(b) => Some(b),
                    _ => None,
                },
            },
            _ => match self.evaluate_term(model, t) {
                EvalValue::Bool(b) => Some(b),
                _ => None,
            },
        }
    }

    /// W2b (bridge route) — argument-VALUE congruence index over the ground
    /// core's committed UF applications: `(symbol, [definite arg atoms]) →
    /// (application TermId, definite result atom)`. Built from the ORIGINAL
    /// (pre-rewrite) ground assertions, whose application TermIds carry the
    /// candidate model's committed per-application values.
    ///
    /// SOUNDNESS: reading the index is only ever used to substitute one
    /// application for another whose arguments have the SAME definite values
    /// under the ONE completed model M' — function congruence makes the two
    /// applications denote the same object in M', for ANY function symbol.
    /// A key whose committed rows disagree (two apps, same arg values,
    /// different result values) is POISONED (`None`) and never used —
    /// fail-closed against an inconsistent-model surprise.
    fn dt_cert_build_uf_value_index(
        &self,
        model: &Model,
        grounds: &[TermId],
    ) -> HashMap<(String, Vec<String>), Option<(TermId, String)>> {
        let mut index: HashMap<(String, Vec<String>), Option<(TermId, String)>> =
            HashMap::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = grounds.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, a, b) => {
                    stack.push(c);
                    stack.push(a);
                    stack.push(b);
                }
                TermData::App(sym, args) => {
                    stack.extend(args.iter().copied());
                    if args.is_empty() || !is_mbqi_completable_uf_symbol(sym.name()) {
                        continue;
                    }
                    let Some(arg_atoms) = args
                        .iter()
                        .map(|&a| self.dt_cert_scalar_atom(&self.evaluate_term(model, a)))
                        .collect::<Option<Vec<String>>>()
                    else {
                        continue;
                    };
                    let Some(result_atom) = self.dt_cert_scalar_atom(&self.evaluate_term(model, t))
                    else {
                        continue;
                    };
                    let key = (sym.name().to_string(), arg_atoms);
                    match index.get_mut(&key) {
                        None => {
                            index.insert(key, Some((t, result_atom)));
                        }
                        Some(slot) => {
                            if let Some((_, prev)) = slot {
                                if *prev != result_atom {
                                    // Conflicting committed rows: poison.
                                    *slot = None;
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        index
    }

    /// W2b (bridge route) — rewrite every INDEFINITE application in `t` whose
    /// (symbol, definite argument values) key matches a committed ground-core
    /// application (`dt_cert_build_uf_value_index`) to THAT application's
    /// TermId, so `evaluate_term` resolves it through the committed model
    /// value. Definite applications are left untouched (the single-authority
    /// evaluator already owns them); an unmatched indefinite application stays
    /// as-is (and the ground stays fail-closed indefinite). Sound by function
    /// congruence under the one completed model M' — see the index builder.
    fn dt_cert_congruence_rewrite(
        &mut self,
        model: &Model,
        t: TermId,
        index: &HashMap<(String, Vec<String>), Option<(TermId, String)>>,
        memo: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let result = match self.ctx.terms.get(t).clone() {
            TermData::Not(i) => {
                let ri = self.dt_cert_congruence_rewrite(model, i, index, memo);
                self.ctx.terms.mk_not(ri)
            }
            TermData::Ite(c, a, b) => {
                let rc = self.dt_cert_congruence_rewrite(model, c, index, memo);
                let ra = self.dt_cert_congruence_rewrite(model, a, index, memo);
                let rb = self.dt_cert_congruence_rewrite(model, b, index, memo);
                self.ctx.terms.mk_ite(rc, ra, rb)
            }
            TermData::App(sym, args) => {
                let mut new_args: Vec<TermId> = Vec::with_capacity(args.len());
                for a in &args {
                    new_args.push(self.dt_cert_congruence_rewrite(model, *a, index, memo));
                }
                let sort = self.ctx.terms.sort(t).clone();
                let rebuilt = self.ctx.terms.mk_app(sym.clone(), new_args.clone(), sort);
                if !new_args.is_empty()
                    && is_mbqi_completable_uf_symbol(sym.name())
                    && matches!(self.evaluate_term(model, rebuilt), EvalValue::Unknown)
                {
                    if let Some(arg_atoms) = new_args
                        .iter()
                        .map(|&a| self.dt_cert_scalar_atom(&self.evaluate_term(model, a)))
                        .collect::<Option<Vec<String>>>()
                    {
                        if let Some(Some((committed, _))) =
                            index.get(&(sym.name().to_string(), arg_atoms))
                        {
                            memo.insert(t, *committed);
                            return *committed;
                        }
                    }
                }
                rebuilt
            }
            _ => t,
        };
        memo.insert(t, result);
        result
    }

    /// Rewrite every F3 bridge-UF application `bridge(a)` in `t` to its declared
    /// selector `sel(a)` (the symbolic default that closes the bridge). Identity
    /// when `bridge_rewrite` is empty (⇒ byte-identical M1 behaviour). This IS
    /// the completed model M' materialized as a term rewrite: evaluating the
    /// rewritten term under `model` yields the M' value.
    fn dt_cert_bridge_rewrite(
        &mut self,
        t: TermId,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
        memo: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if bridge_rewrite.is_empty() {
            return t;
        }
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let result = match self.ctx.terms.get(t).clone() {
            TermData::Not(i) => {
                let ri = self.dt_cert_bridge_rewrite(i, bridge_rewrite, memo);
                self.ctx.terms.mk_not(ri)
            }
            TermData::Ite(c, a, b) => {
                let rc = self.dt_cert_bridge_rewrite(c, bridge_rewrite, memo);
                let ra = self.dt_cert_bridge_rewrite(a, bridge_rewrite, memo);
                let rb = self.dt_cert_bridge_rewrite(b, bridge_rewrite, memo);
                self.ctx.terms.mk_ite(rc, ra, rb)
            }
            TermData::App(sym, args) => {
                let mut new_args: Vec<TermId> = Vec::with_capacity(args.len());
                for a in &args {
                    new_args.push(self.dt_cert_bridge_rewrite(*a, bridge_rewrite, memo));
                }
                if args.len() == 1 {
                    if let Some((sel_name, field_sort)) = bridge_rewrite.get(sym.name()) {
                        let r = self.ctx.terms.mk_app(
                            Symbol::named(sel_name.as_str()),
                            [new_args[0]],
                            field_sort.clone(),
                        );
                        memo.insert(t, r);
                        return r;
                    }
                }
                let sort = self.ctx.terms.sort(t).clone();
                self.ctx.terms.mk_app(sym, new_args, sort)
            }
            _ => t,
        };
        memo.insert(t, result);
        result
    }

    /// Render a certified table value in the atom spelling the EUF extraction
    /// uses for committed function/class values (`eval_value_to_model_atom`), so
    /// a cert cell can be compared for equality against a committed atom read.
    fn dt_cert_table_val_atom(v: &TableCertVal) -> String {
        match v {
            TableCertVal::Int(i) => i.to_string(),
            TableCertVal::Bool(b) => b.to_string(),
            TableCertVal::Rat(r) => {
                if r.is_integer() {
                    r.numer().to_string()
                } else {
                    format!("(/ {} {})", r.numer(), r.denom())
                }
            }
        }
    }

    /// EUF-EXTRACTION FAITHFULNESS GUARANTEE (SAT-side base-recheck campaign,
    /// blocking pin #5) — the last soundness prerequisite before an authoritative
    /// DT-cert grant. Runs at cert-grant time, BEFORE any grant (shadow or
    /// authoritative). Read-only (`&self`): a cheap pass over already-committed
    /// state (~71-100 ground asserts), no minting.
    ///
    /// THE HOLE it closes (the [[regression-mutref-euf-lia-model]] class): the F4
    /// tables are built with `evaluate_term`, which resolves an Int UF
    /// application through the arg-keyed function-table synthesis. A
    /// ground-pinned value that reaches the solver only IMPLICITLY (via EUF
    /// equality/congruence chains not materialized as a directly-evaluable
    /// ground assertion) could be DROPPED or MISASSIGNED there — the table cell
    /// then disagrees with the solver's committed e-graph value, no single
    /// ground assertion evaluates false, and F4 certifies a universal the true
    /// model violates → wrong-SAT → a vacuous proof reports Verified (the
    /// cardinal sin).
    ///
    /// THE GUARANTEE: for every symbol the certificate RELIES ON (the F4 finite-
    /// table symbols + the W1/W2 bridge UFs), cross-check the cert's decision
    /// against the solver's COMMITTED per-application value read through
    /// [`Executor::committed_app_atom`] — the NON-RECURSIVE `func_app_const_terms`
    /// / `int_values` / `term_values` anchors, INDEPENDENT of the arg-keyed
    /// table synthesis that produced the cert cell. An extraction that
    /// dropped/misassigned a row can no longer produce a certified grant,
    /// because the certification now requires and cross-checks a committed
    /// source of truth rather than trusting the extracted table alone.
    ///
    /// Fail-closed. DECLINE (`Err`) on: (1) any relied-upon symbol the EUF
    /// extraction flagged as a cross-theory function-table conflict
    /// (`function_table_conflicts` — its own contract says consumers MUST fail
    /// closed); (2) any ground-core application whose committed value disagrees
    /// with the certified cell at its argument e-class; (3) congruent
    /// applications (same argument e-class) that commit two different values (the
    /// dropped-congruence signature); (4) an argument whose e-class cannot be
    /// resolved; (5) a ground application with no independent committed anchor;
    /// (6) a ground application with no certified row or default. The final two
    /// cases MUST decline: accepting either would reduce this purportedly
    /// independent check to trusting the same evaluator/table extraction whose
    /// omission or misassignment it exists to catch.
    fn dt_cert_extraction_faithful(
        &self,
        model: &Model,
        snapshot: &[TermId],
        table_syms: &HashMap<String, TableCertSort>,
        tables: &HashMap<String, HashMap<String, TableCertVal>>,
        defaults: &HashMap<String, TableCertVal>,
        bridge_rewrite: &HashMap<String, (String, Sort)>,
    ) -> std::result::Result<(), String> {
        // The cert's F4 tables and bridge completion are over UF applications
        // whose committed values live in the EUF model. With no EUF model there
        // is no committed surface to certify against — fail closed if the cert
        // relied on any table or bridge symbol.
        let Some(euf) = model.euf_model.as_ref() else {
            if table_syms.is_empty() && bridge_rewrite.is_empty() {
                return Ok(());
            }
            return Err("no EUF model to cross-check tabled/bridge symbols".to_string());
        };

        // (1) Cross-theory function-table conflicts. The extraction flags a
        // symbol whose rows became semantically inconsistent after model
        // combination and could not be repaired exactly; certifying a universal
        // over such a symbol is the wrong-SAT vector its contract warns of.
        for uf in table_syms.keys().chain(bridge_rewrite.keys()) {
            if euf.function_table_conflicts.contains(uf) {
                return Err(format!(
                    "committed function table for `{uf}` is flagged inconsistent \
                     (cross-theory merge conflict)"
                ));
            }
        }

        // (2)+(3) Committed-vs-certified agreement + congruence consistency over
        // every ground-core application of a relied-upon table symbol.
        let mut committed_by_key: HashMap<(String, String), String> = HashMap::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = snapshot.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, b) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    let name = sym.name().to_string();
                    let args = args.clone();
                    stack.extend(args.iter().copied());
                    if !table_syms.contains_key(&name) || args.len() != 1 {
                        continue;
                    }
                    // Skip the certified BINDER application `uf(x)` (and any
                    // binder-DEPENDENT `uf(g(x))`): its argument is a bound
                    // variable with no committed e-class, so it is the universal
                    // itself, not a ground observation — step 4 (`dt_cert_value_
                    // key`) skips it too. Every GROUND table argument DID resolve
                    // (else step 4 would already have declined "unresolvable
                    // e-class key for a table arg" before we reached the grant),
                    // so a `None` here is exactly a non-ground application.
                    let Some(key) = self.dt_cert_value_key(model, args[0]) else {
                        continue;
                    };
                    // Committed per-application value (the independent anchor
                    // read). A ground application with no anchor is not
                    // certifiable: falling back to the evaluator here would be
                    // circular, because that evaluator produced the F4 cell.
                    let Some(atom) = self.committed_app_atom(model, euf, t) else {
                        return Err(format!(
                            "`{name}` has no independent committed value at argument e-class `{key}`"
                        ));
                    };
                    // The certified decision at this cell (what an F4 body would
                    // have substituted for `uf(x)` at this e-class).
                    let Some(cell) = tables
                        .get(&name)
                        .and_then(|tab| tab.get(&key))
                        .cloned()
                        .or_else(|| defaults.get(&name).cloned())
                    else {
                        return Err(format!(
                            "`{name}` has no certified row or default at argument e-class `{key}`"
                        ));
                    };
                    let cell_atom = Self::dt_cert_table_val_atom(&cell);
                    if cell_atom != atom {
                        return Err(format!(
                            "`{name}` committed value `{atom}` disagrees with certified \
                             cell `{cell_atom}` at argument e-class `{key}`"
                        ));
                    }
                    // Congruence: two applications whose arguments share an
                    // e-class must commit ONE value (a disagreement is the
                    // dropped-congruence extraction signature).
                    match committed_by_key.get(&(name.clone(), key.clone())) {
                        Some(prev) if *prev != atom => {
                            return Err(format!(
                                "`{name}` congruent applications commit two values \
                                 (`{prev}` vs `{atom}`) at argument e-class `{key}`"
                            ));
                        }
                        _ => {
                            committed_by_key.insert((name.clone(), key), atom);
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// After a re-sequencing grant, drop the legacy/raw function-table artifacts
    /// of every completable UF that heads a top-level `forall` in `snapshot`.
    /// Those tables came from the ground-core candidate, so their arbitrary
    /// defaults do not witness the universal.  An exact typed total
    /// interpretation installed by this certificate is deliberately preserved:
    /// it is the completed M′ that was proved and is authoritative for both
    /// evaluation and model output.
    ///
    /// Authority invariant: callers may invoke this only immediately after
    /// `try_dt_model_sat_certificate(snapshot, ..)` returned `Some`. This
    /// cleanup does not mint or extend a grant; it only removes raw rows
    /// superseded by certificate-owned typed interpretations. The public SAT
    /// path records the grant after this function returns.
    ///
    /// Selector/constructor/tester heads are left untouched (they are
    /// DT-interpreted, not free UFs). The per-application ground pins the strict /
    /// independent / authoritative gates read for the GROUND assertions survive
    /// (they are authoritative over the arg-keyed table), so ground validation is
    /// unaffected. Only runs on the AY_DT_CERT grant path.
    pub(in crate::executor) fn dt_cert_strip_forall_uf_tables(&mut self, snapshot: &[TermId]) {
        let mut heads: HashSet<String> = HashSet::default();
        for &a in snapshot {
            let TermData::Forall(_, body, _) = self.ctx.terms.get(a) else {
                continue;
            };
            let body = *body;
            let mut visited: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = vec![body];
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                if let TermData::App(sym, args) = self.ctx.terms.get(t) {
                    let name = sym.name();
                    // Every arity>0 head that appears in a forall: stale raw
                    // rows can otherwise compete with certificate-installed M′
                    // or make a non-materialized certificate look model-complete.
                    // Typed certified interpretations and per-application ground
                    // pins are separate model data and survive this cleanup.
                    if !args.is_empty() {
                        heads.insert(name.to_string());
                    }
                    stack.extend(args.iter().copied());
                } else {
                    match self.ctx.terms.get(t) {
                        TermData::Not(i) => stack.push(*i),
                        TermData::Ite(c, x, y) => {
                            stack.push(*c);
                            stack.push(*x);
                            stack.push(*y);
                        }
                        _ => {}
                    }
                }
            }
        }
        if heads.is_empty() {
            return;
        }
        if let Some(model) = self.last_model.as_mut() {
            for h in &heads {
                // Only the F4 head replaced by a certificate-owned typed M'
                // has a stale raw table.  G-route consequents and x-free F4
                // support expressions may read unrelated UFs whose incoming
                // raw interpretations are part of the model the certificate
                // checked; deleting those would publish a different model.
                if model.has_certified_total_uf(h) {
                    model.remove_raw_uf_table_interpretation(h);
                }
            }
        }
    }

    // =====================================================================
    // CONSTANT-INTERPRETATION SAT certificate (`AY_CONST_INTERP_CERT`).
    // =====================================================================

    /// # The CONSTANT-INTERPRETATION SAT certificate (grant-only)
    ///
    /// For a snapshot whose assertions are ALL top-level `forall`s, pick a
    /// candidate interpretation `I` mapping some uninterpreted heads to
    /// CONSTANT functions, substitute `I` into each quantified body, replace
    /// the binders with FRESH constants, and require the NEGATED body to be
    /// UNSAT. That proves the body valid under `I` for every binder value, so
    /// `I` satisfies every axiom, so the snapshot is `Sat`.
    ///
    /// ## Why this is a certificate and not a model guesser
    ///
    /// Candidate SELECTION — which heads, which constants, in which order — is
    /// a pure heuristic that is never trusted: a bug there can only lose a
    /// grant we could have had, never manufacture one we could not. Each
    /// candidate must still DISCHARGE every axiom, in one of exactly two ways:
    ///
    /// - (A) the substituted body is the literal constant `true`, i.e. the
    ///   `mk_*` rebuild folded it outright. Trusted base: the constructors'
    ///   documented contract that every rewrite they perform is
    ///   semantics-preserving. This is the strongest form — the body is a
    ///   syntactic tautology under `I` — and it is what discharges the simplest
    ///   axioms (`∀s. 0 <= seq_len(s)` under `seq_len := 0` folds to `true`
    ///   with NO nested solve at all).
    /// - (B) otherwise, an `Unsat` on the negated body from
    ///   [`Self::checked_ground_solve`], AY's checked fail-closed ground
    ///   funnel. Trusted base: that `Unsat`.
    ///
    /// Both legs are checked per axiom; a combination is accepted only when
    /// EVERY axiom passes one of them. The single genuine soundness surface
    /// they share is the SUBSTITUTION, which is why
    /// [`Self::const_interp_substitution`] is deliberately mechanical and
    /// commented line by line.
    ///
    /// ## The theorem, spelled out
    ///
    /// Let the snapshot be `A_1 .. A_n` with `A_j = ∀ x̄_j. B_j(x̄_j)`, every
    /// `B_j` quantifier-free. Let `I` map a set `H` of uninterpreted heads
    /// `f ↦ c_f` where each `c_f` is a CLOSED term of `f`'s result sort, and
    /// let `I(f)` denote the constant function `λ ȳ. c_f`. Write `B_j[I]` for
    /// `B_j` with every application `f(t̄)`, `f ∈ H`, rewritten to `c_f`, and
    /// `k̄_j` for a vector of constants FRESH everywhere.
    ///
    /// Suppose that for every `j` the ground solver reports
    /// `¬ B_j[I][x̄_j := k̄_j]` UNSAT. Fix any interpretation `J` of the
    /// symbols NOT in `H` (residual heads, and there is always at least one
    /// such `J` because SMT-LIB sorts are non-empty). If some `ā` in the
    /// binder domain made `B_j` false under `I ∪ J`, then extending `J` with
    /// `k̄_j := ā` would satisfy `¬ B_j[I][k̄_j]` — contradicting UNSAT, which
    /// says NO interpretation of that formula's free symbols satisfies it.
    /// Hence `I ∪ J ⊨ ∀ x̄_j. B_j` for every `j`.
    ///
    /// The `j`s share ONE `I` (the combination loop assigns each head a single
    /// value across all axioms), and `J` is arbitrary, so a single structure
    /// `I ∪ J` satisfies the WHOLE snapshot simultaneously. The snapshot is
    /// therefore `Sat`, and since the consult sites pass a snapshot that is
    /// the original assertions plus their instantiation consequences, the
    /// original problem is `Sat`.
    ///
    /// ## Fail-closed perimeter
    ///
    /// Everything below returns `None` (decline):
    /// - a non-`forall` assertion anywhere in the snapshot (so any GROUND
    ///   assertion declines — the theorem above is stated for an all-`forall`
    ///   problem and is not extended here);
    /// - an `exists`, a nested quantifier, or a `let` inside a body;
    /// - a `no_mbqi` (Hilbert-choose / E-matching-only) `forall`;
    /// - a non-`Bool` body, an empty binder list;
    /// - any `TermData` variant not explicitly handled (including future ones);
    /// - a head whose result sort has no closed constant candidate is simply
    ///   LEFT UNINTERPRETED (sound: `J` ranges over it), but a head whose
    ///   occurrences disagree on sort or arity declines;
    /// - more than [`MAX_CONST_INTERP_HEADS`] interpreted heads, more than
    ///   [`MAX_CONST_INTERP_COMBOS`] combinations, more than
    ///   [`MAX_CONST_INTERP_SOLVER_CALLS`] nested solves, or the wall-clock
    ///   budget expiring;
    /// - re-entrancy: a nested validity solve that reaches this function again
    ///   declines at depth > 0 (see [`CONST_INTERP_CERT_DEPTH`]);
    /// - WITNESS: when nothing else produced a model (`last_model` was `None` at
    ///   entry), a pinned head whose interpretation cannot be rendered as a
    ///   `(define-fun ...)` under the name `(get-model)` looks for — see
    ///   [`Self::const_interp_witness_shape`]. The certificate is the sole
    ///   source of a model on that route, and `I` is ONE structure: publishing
    ///   it minus a head is not a witness, so the whole certificate declines.
    ///
    /// Grant-only: this function returns `Some(())` or `None`. It never
    /// produces, influences, or blocks an `Unsat` verdict.
    ///
    /// ## The model it grants
    ///
    /// On every grant, the certificate installs `I` itself:
    /// [`Self::install_const_interp_cert_witness`] records the pinned heads as
    /// printable model entries and completes every other declared symbol with
    /// [`Self::completed_default_model`] — a concrete `J`, which the theorem
    /// admits because it holds for EVERY `J`. `(get-model)` then reports the
    /// interpretation the certificate actually checked, and the evaluator reads
    /// the same one, so `(get-value)` cannot contradict it.
    /// CLOSED-VALID-SENTENCE SAT certificate.
    ///
    /// Discharges two independently checked CLOSED theorem families that the
    /// quantified fail-closed gate cannot witness with a model:
    ///
    /// `forall x:Int. (x mod 2 = 0 or (x + 1) mod 2 = 0)`.
    ///
    /// `forall x:Int. exists y:Int. x < y`, optionally conjoined with
    /// `C < y` for one integer literal `C`.
    ///
    /// Binder names and harmless commutative orderings may differ, but every
    /// sort, literal, core operator, binder occurrence, trigger list, and
    /// connective shape is rechecked structurally. Everything else declines.
    ///
    /// ## Why this class needs its own certificate
    ///
    /// `apply_quantified_model_failclosed_gate` confirms a quantified
    /// assertion by evaluating it against the EMITTED MODEL. A symbol-free
    /// closed sentence has no model entry to pin, so that gate correctly
    /// defers. This certificate supplies theorem evidence for the exact parity
    /// families rather than pretending that a sampled quantifier-elimination
    /// result is a proof.
    ///
    /// ## Soundness
    ///
    /// For every integer `x`, SMT-LIB's positive-modulus remainder `x mod 2`
    /// is either `0` or `1`. In the first case the left disjunct holds; in the
    /// second, `(x + 1) mod 2 = 0` holds. The checker admits exactly those two
    /// residue tests over the same bound-`Int` term. It calls no solver, QE
    /// pass, sampler, or candidate generator, so none of those mechanisms can
    /// mint this authority.
    ///
    /// For the unbounded-above family, `y := x + 1` witnesses the one-atom
    /// form. With literal `C`, `y := max(x, C) + 1` is greater than both `x`
    /// and `C`. The recognizer requires exactly those lower-bound atoms, so the
    /// constructive proof covers the complete admitted matrix.
    ///
    /// ## Fail-closed perimeter
    ///
    /// - GRANT-ONLY: returns `None` on every doubt; a decline leaves the
    ///   caller's verdict exactly as it was.
    /// - The outer partition is still checked SYNTACTICALLY on the sentence
    ///   ([`Self::closed_sentence_without_uninterpreted_symbols`]) — "no
    ///   uninterpreted head" means the term genuinely contains none, NOT that
    ///   the model failed to pin one. That distinction is the whole soundness
    ///   margin: keying off "the witness pinned nothing" would rubber-stamp
    ///   the auflia-model escape class (∀∃ over a printed `f`), where
    ///   substitution consumes every model symbol and leaves nothing to pin.
    ///   A single declared symbol anywhere in the sentence — constant or
    ///   function, under any binder — declines.
    /// - The interpreted operator spellings are rejected if any source
    ///   declaration shadows them. Every application must carry the exact
    ///   canonical core identity and sort.
    /// - Different moduli, offsets, connectives, extra binders, nested
    ///   quantifiers, triggers, or additional assertion shapes all decline.
    pub(in crate::executor) fn try_valid_closed_sentence_sat_certificate(
        &mut self,
        snapshot: &[TermId],
        _fallback_category: LogicCategory,
    ) -> Option<CheckedExactClosedSentenceSat> {
        let debug = ay_core::misc_cli_flags().debug_cert;
        if snapshot.is_empty() {
            return None;
        }
        // Never extend a solve that is already past its deadline/interrupt.
        if self.external_stop_reason().is_some() {
            return None;
        }
        // At least one quantifier, or this is a ground problem the ordinary
        // pipeline already owns end-to-end (and whose model the gate can check
        // without help). Cheapest discriminator, so it runs first.
        if !snapshot
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
        {
            return None;
        }
        // ---- PARTITION: every assertion closed and free of uninterpreted
        // symbols. Checked before the exact theorem recognizer. The
        // declared-symbol set is built ONCE and shared across the assertions —
        // rebuilding it per assertion would be O(assertions x symbols) on a
        // snapshot that never mentions a declared symbol.
        let declared: HashSet<String> = self
            .ctx
            .symbol_iter()
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        if !self.exact_closed_sentence_operators_are_unshadowed() {
            if debug {
                eprintln!(
                    "CERT/valid-sentence decline: closed-sentence operator is source-shadowed"
                );
            }
            return None;
        }
        let mut needs_refutation_evidence: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            if !self.closed_sentence_without_uninterpreted_symbols(assertion, &declared) {
                if debug {
                    eprintln!(
                        "CERT/valid-sentence decline: {assertion:?} is not a closed sentence \
                         free of uninterpreted symbols"
                    );
                }
                return None;
            }
            if !self.is_exact_closed_parity_theorem(assertion)
                && !self.is_exact_closed_unbounded_above_theorem(assertion)
            {
                needs_refutation_evidence.push(assertion);
            }
        }
        // ---- GENERAL ARM (#closed-sentence-cert): a closed sentence outside
        // the two structural recognizers is proven valid by REFUTING ITS
        // NEGATION through the checked reconfirmation primitive — fresh
        // executor, deterministic conflict/decision bounds, structural proof
        // screen. Validity implies satisfiability for a closed sentence
        // (SMT-LIB sorts are non-empty), and a valid sentence has nothing for
        // a witness model to pin, which is exactly why the model gate cannot
        // confirm this class and an authority grant is the right instrument.
        //
        // HISTORY, because this arm was here before and was rightly removed.
        // The pre-2026-08-08 form accepted a bare `Unsat` from a plain
        // isolated solve of the negation — trust, not evidence — and the
        // "harden checked solver authority" merge narrowed the certificate to
        // the two structural families rather than carry that trust forward.
        // The narrowing was correct about the trust and collateral about the
        // class: it starved every restored existential (a trivially
        // satisfiable `exists x. x = 5` published `unknown` with reason
        // `quantifier-ematching-exists`, twelve pinned tests in
        // `skolemization_5840` alike). This arm restores the CLASS with the
        // evidence upgraded to what the funnel itself accepts: the nested
        // refutation must survive the same structural proof screen the
        // deferred-trust discharge uses. Bisected to the merge and verified
        // on both parents; see the a735ef4031 investigation.
        //
        // Kill switch: `--dpll-no-closed-sentence-cert` (default on).
        if !needs_refutation_evidence.is_empty() {
            // B28: CLI-owned (--dpll-no-closed-sentence-cert); the env mode
            // string is retired and the never-exercised `shadow` arm removed.
            if ay_core::theory_disable_flags().no_closed_sentence_cert {
                if debug {
                    eprintln!("CERT/valid-sentence decline: general arm disabled by CLI");
                }
                return None;
            }
            // Binder sorts must be INTERPRETED. The symbol partition above
            // admits a binder over a declared uninterpreted sort (a sort is
            // not a symbol), and the general arm deliberately does not extend
            // there: the structural recognizers never accept one, and widening
            // the class and the evidence in the same change would leave no
            // clean attribution if the sweep moves.
            if !needs_refutation_evidence
                .iter()
                .all(|&a| self.closed_sentence_binder_sorts_are_interpreted(a))
            {
                if debug {
                    eprintln!("CERT/valid-sentence decline: binder over an uninterpreted sort");
                }
                return None;
            }
            for &assertion in &needs_refutation_evidence {
                let negation = self.ctx.terms.mk_not(assertion);
                if !self.reconfirms_negation_refuted_for_closed_sentence(&[negation]) {
                    if debug {
                        eprintln!(
                            "CERT/valid-sentence decline: {assertion:?} negation not \
                             refuted under the checked reconfirmation primitive"
                        );
                    }
                    return None;
                }
            }
        }
        if debug {
            eprintln!(
                "CERT/valid-sentence: certified SAT ({} exact structural theorems)",
                snapshot.len()
            );
        }
        Some(CheckedExactClosedSentenceSat::for_current(self, snapshot))
    }

    /// Every quantifier binder reachable from `root` ranges over an
    /// INTERPRETED sort. Guard for the general closed-sentence arm: the symbol
    /// partition cannot see sorts, and a closed sentence quantifying over a
    /// declared uninterpreted sort stays outside the class until it has its
    /// own measured campaign.
    fn closed_sentence_binder_sorts_are_interpreted(&self, root: TermId) -> bool {
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            match self.ctx.terms.get(term) {
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    if !vars.iter().all(|(_, sort)| {
                        matches!(sort, Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_))
                    }) {
                        return false;
                    }
                    stack.push(*body);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        true
    }

    /// Check the exact interpreted identities used by the structural theorem.
    /// `symbol_iter` exposes stable declaration identities across overloads and
    /// scope incarnations; checking both surface and identity prevents a
    /// builtin-colliding declaration from becoming acceptable merely because
    /// elaboration renamed it internally.
    fn exact_closed_sentence_operators_are_unshadowed(&self) -> bool {
        self.ctx.symbol_iter().all(|(surface, info)| {
            let identity = self.ctx.symbol_identity_name(surface, info);
            !EXACT_CLOSED_SENTENCE_OPERATORS.contains(&surface.as_str())
                && !EXACT_CLOSED_SENTENCE_OPERATORS.contains(&identity)
        })
    }

    /// Exact theorem recognizer for `forall x:Int. even(x) or even(x+1)`.
    fn is_exact_closed_parity_theorem(&self, assertion: TermId) -> bool {
        if self.ctx.terms.entry_stamp(assertion).is_none()
            || self.ctx.terms.sort(assertion) != &Sort::Bool
        {
            return false;
        }
        let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(assertion) else {
            return false;
        };
        let [(binder_name, binder_sort)] = vars.as_slice() else {
            return false;
        };
        if binder_sort != &Sort::Int || !triggers.is_empty() {
            return false;
        }
        let Some((left, right)) = self.exact_closed_binary(*body, "or", &Sort::Bool) else {
            return false;
        };
        let Some((left_binder, left_residue)) = self.exact_closed_parity_residue(left, binder_name)
        else {
            return false;
        };
        let Some((right_binder, right_residue)) =
            self.exact_closed_parity_residue(right, binder_name)
        else {
            return false;
        };
        left_binder == right_binder
            && matches!(
                (left_residue, right_residue),
                (
                    ExactClosedParityResidue::Binder,
                    ExactClosedParityResidue::Successor
                ) | (
                    ExactClosedParityResidue::Successor,
                    ExactClosedParityResidue::Binder
                )
            )
    }

    /// Exact theorem recognizer for
    /// `forall x:Int. exists y:Int. x<y [and C<y]`.
    fn is_exact_closed_unbounded_above_theorem(&self, assertion: TermId) -> bool {
        if self.ctx.terms.entry_stamp(assertion).is_none()
            || self.ctx.terms.sort(assertion) != &Sort::Bool
        {
            return false;
        }
        let TermData::Forall(forall_vars, exists, forall_triggers) = self.ctx.terms.get(assertion)
        else {
            return false;
        };
        let [(universal_name, universal_sort)] = forall_vars.as_slice() else {
            return false;
        };
        if universal_sort != &Sort::Int || !forall_triggers.is_empty() {
            return false;
        }
        let TermData::Exists(exists_vars, body, exists_triggers) = self.ctx.terms.get(*exists)
        else {
            return false;
        };
        let [(existential_name, existential_sort)] = exists_vars.as_slice() else {
            return false;
        };
        if existential_sort != &Sort::Int
            || universal_name == existential_name
            || !exists_triggers.is_empty()
        {
            return false;
        }

        if matches!(
            self.exact_closed_unbounded_lower(*body, universal_name, existential_name),
            Some((_, ExactClosedUnboundedLower::Universal))
        ) {
            return true;
        }

        let Some((left, right)) = self.exact_closed_binary(*body, "and", &Sort::Bool) else {
            return false;
        };
        let Some((left_y, left_lower)) =
            self.exact_closed_unbounded_lower(left, universal_name, existential_name)
        else {
            return false;
        };
        let Some((right_y, right_lower)) =
            self.exact_closed_unbounded_lower(right, universal_name, existential_name)
        else {
            return false;
        };
        left_y == right_y
            && matches!(
                (left_lower, right_lower),
                (
                    ExactClosedUnboundedLower::Universal,
                    ExactClosedUnboundedLower::Literal
                ) | (
                    ExactClosedUnboundedLower::Literal,
                    ExactClosedUnboundedLower::Universal
                )
            )
    }

    /// Recognize one strict lower bound on the existential witness. The right
    /// side must be the exact bound `Int` term; the left side is either the
    /// universal binder or one closed integer literal.
    fn exact_closed_unbounded_lower(
        &self,
        atom: TermId,
        universal_name: &str,
        existential_name: &str,
    ) -> Option<(TermId, ExactClosedUnboundedLower)> {
        let (lower, witness) = self.exact_closed_binary(atom, "<", &Sort::Bool)?;
        let witness = self.exact_closed_bound_int(witness, existential_name)?;
        if self.exact_closed_bound_int(lower, universal_name).is_some() {
            return Some((witness, ExactClosedUnboundedLower::Universal));
        }
        if self.ctx.terms.entry_stamp(lower).is_some()
            && self.ctx.terms.sort(lower) == &Sort::Int
            && matches!(self.ctx.terms.get(lower), TermData::Const(Constant::Int(_)))
        {
            return Some((witness, ExactClosedUnboundedLower::Literal));
        }
        None
    }

    /// Recognize one equality-to-zero residue test and return the exact bound
    /// variable term it contains.
    fn exact_closed_parity_residue(
        &self,
        term: TermId,
        binder_name: &str,
    ) -> Option<(TermId, ExactClosedParityResidue)> {
        let (left, right) = self.exact_closed_binary(term, "=", &Sort::Bool)?;
        let modulo = if self.exact_closed_int_constant(right, 0) {
            left
        } else if self.exact_closed_int_constant(left, 0) {
            right
        } else {
            return None;
        };
        let (numerator, modulus) = self.exact_closed_binary(modulo, "mod", &Sort::Int)?;
        if !self.exact_closed_int_constant(modulus, 2) {
            return None;
        }
        if let Some(bound) = self.exact_closed_bound_int(numerator, binder_name) {
            return Some((bound, ExactClosedParityResidue::Binder));
        }

        let (left, right) = self.exact_closed_binary(numerator, "+", &Sort::Int)?;
        let bound = if self.exact_closed_int_constant(right, 1) {
            self.exact_closed_bound_int(left, binder_name)?
        } else if self.exact_closed_int_constant(left, 1) {
            self.exact_closed_bound_int(right, binder_name)?
        } else {
            return None;
        };
        Some((bound, ExactClosedParityResidue::Successor))
    }

    fn exact_closed_bound_int(&self, term: TermId, binder_name: &str) -> Option<TermId> {
        self.ctx.terms.entry_stamp(term)?;
        if self.ctx.terms.sort(term) != &Sort::Int {
            return None;
        }
        matches!(
            self.ctx.terms.get(term),
            TermData::Var(name, _) if name == binder_name
        )
        .then_some(term)
    }

    fn exact_closed_int_constant(&self, term: TermId, expected: i64) -> bool {
        self.ctx.terms.entry_stamp(term).is_some()
            && self.ctx.terms.sort(term) == &Sort::Int
            && matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Int(value))
                    if value == &num_bigint::BigInt::from(expected)
            )
    }

    fn exact_closed_binary(
        &self,
        term: TermId,
        expected_operator: &str,
        expected_sort: &Sort,
    ) -> Option<(TermId, TermId)> {
        self.ctx.terms.entry_stamp(term)?;
        if self.ctx.terms.sort(term) != expected_sort {
            return None;
        }
        let TermData::App(Symbol::Named(operator), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        (operator == expected_operator).then_some((*left, *right))
    }

    /// Partition test for [`Self::try_valid_closed_sentence_sat_certificate`]:
    /// `root` is a CLOSED sentence (every `Var` bound by an enclosing binder)
    /// that mentions NO user-declared symbol of any arity.
    ///
    /// Declared CONSTANTS count. `∀x:Int. x >= c` pins nothing and is not
    /// valid; admitting arity-0 symbols would hand the certificate a sentence
    /// whose truth genuinely depends on an interpretation. Excluding them
    /// keeps "nothing to interpret" literally true.
    ///
    /// FAIL-CLOSED on everything it does not model exactly: an unexpanded
    /// `Let`, or a term larger than [`VALID_SENTENCE_PARTITION_NODE_CAP`]
    /// visits, declines. The walk carries the binder scope explicitly and does
    /// NOT memoise — memoising by `TermId` alone would conflate a shared
    /// subterm's different scopes and could accept a free variable.
    fn closed_sentence_without_uninterpreted_symbols(
        &self,
        root: TermId,
        declared: &HashSet<String>,
    ) -> bool {
        let mut stack: Vec<(TermId, Vec<String>)> = vec![(root, Vec::new())];
        let mut visits: u32 = 0;
        while let Some((term, bound)) = stack.pop() {
            visits += 1;
            if visits > VALID_SENTENCE_PARTITION_NODE_CAP {
                return false;
            }
            match self.ctx.terms.get(term) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    if !bound.iter().any(|b| b == name) {
                        return false;
                    }
                }
                TermData::App(sym, args) => {
                    if declared.contains(sym.name()) {
                        return false;
                    }
                    let args = args.clone();
                    for a in args {
                        stack.push((a, bound.clone()));
                    }
                }
                TermData::Not(inner) => {
                    let inner = *inner;
                    stack.push((inner, bound));
                }
                TermData::Ite(c, t, e) => {
                    let (c, t, e) = (*c, *t, *e);
                    stack.push((c, bound.clone()));
                    stack.push((t, bound.clone()));
                    stack.push((e, bound));
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    let names: Vec<String> = vars.iter().map(|(v, _)| v.clone()).collect();
                    let body = *body;
                    let triggers: Vec<TermId> =
                        triggers.iter().flat_map(|g| g.iter().copied()).collect();
                    let mut inner = bound;
                    inner.extend(names);
                    for t in triggers {
                        stack.push((t, inner.clone()));
                    }
                    stack.push((body, inner));
                }
                // Unexpanded `Let` is not modelled here — decline rather than
                // guess at its scoping. `TermData` is `#[non_exhaustive]`, so
                // the wildcard catches any variant added later: an unmodelled
                // node must DECLINE, never be silently treated as symbol-free.
                TermData::Let(..) => return false,
                _ => return false,
            }
        }
        true
    }

    pub(in crate::executor) fn try_const_interp_sat_certificate(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<()> {
        // `AY_CONST_INTERP_CERT` gate. `Off` => byte-identical (no scan, no
        // mint, no nested solve, no log).
        let mode = const_interp_cert_mode();
        if matches!(mode, ConstInterpCertMode::Off) {
            return None;
        }
        // Never extend a solve that is already past its deadline/interrupt.
        if self.external_stop_reason().is_some() {
            return None;
        }

        // RE-ENTRANCY (requirement 2, modelled on `TRUST_DISCHARGE_DEPTH`).
        // The accepting step is a nested solve, and a nested solve can reach
        // the quantifier lane's certificate consult sites. Depth 0 only: a
        // nested validity solve must never recurse back into this certificate.
        // A `&mut self` flag would NOT do — `checked_ground_solve`
        // is in-place today, but any future fresh-`Executor` probe resets
        // every field, and a thread-local survives that.
        if CONST_INTERP_CERT_DEPTH.with(|depth| depth.get()) > 0 {
            return None;
        }

        // WITNESS REQUIRED. The theorem establishes one interpretation `I`, so
        // that exact interpretation must replace any raw model already retained
        // by the ground/CEGQI lane. Existence of `I` does not make a different
        // candidate model satisfy the universals. Step 3b therefore requires a
        // printable entry for every pinned head on every route, and the grant
        // parks `I` for atomic installation at the public SAT funnel.
        struct DepthGuard;
        impl Drop for DepthGuard {
            fn drop(&mut self) {
                CONST_INTERP_CERT_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
            }
        }
        CONST_INTERP_CERT_DEPTH.with(|depth| depth.set(depth.get() + 1));
        let _depth_guard = DepthGuard;

        // WALL-CLOCK BUDGET. Never EXTEND the enclosing solve's deadline —
        // take the earlier of (outer deadline, our slice), and restore the
        // outer one on every exit path (the `outcome` binding below is the
        // single return).
        let saved_deadline = self.solve_deadline.get();
        let slice = ay_core::time::Instant::now()
            + std::time::Duration::from_millis(CONST_INTERP_CERT_BUDGET_MS);
        self.set_deadline(match saved_deadline {
            Some(d) if d < slice => Some(d),
            _ => Some(slice),
        });
        // TWO PASSES, STRICTLY ADDITIVE.
        //
        // Pass 1 is EXACTLY the certificate as it was: the fixed closed-constant
        // family (`false/true`, `0/1`, const-`0` array) per head. Every snapshot
        // that grants today grants here, in the same combination order, under
        // the same budgets — byte-identical.
        //
        // Pass 2 runs ONLY when pass 1 declined, and only widens the CANDIDATE
        // SET (see `const_interp_widened_candidates`): the constants the PROBLEM
        // ITSELF already names for a head. Nothing else moves — same partition,
        // same accepting step (substitute `I`, refute the negated body with an
        // independent solver `Unsat`), same witness-shape guard, same wall-clock
        // slice (`slice` is shared, so pass 2 can only use what pass 1 left).
        //
        // Running it as a SECOND pass rather than a bigger first pass is
        // deliberate: extra candidates enlarge the mixed-radix combination
        // space, which would push some of today's grants past
        // `MAX_CONST_INTERP_COMBOS` / `MAX_CONST_INTERP_SOLVER_CALLS` and turn
        // them into declines. A certificate must never LOSE a grant to a
        // widening.
        let outcome = self
            .const_interp_cert_inner(
                snapshot,
                fallback_category,
                mode,
                slice,
                ConstInterpCandidateSource::FixedFamily,
            )
            .or_else(|| {
                self.const_interp_cert_inner(
                    snapshot,
                    fallback_category,
                    mode,
                    slice,
                    ConstInterpCandidateSource::WithProblemConstants,
                )
            });
        self.set_deadline(saved_deadline);
        outcome
    }

    /// Extra candidate constants for one head, drawn from the PROBLEM ITSELF.
    ///
    /// # Why this is not a soundness surface
    ///
    /// A candidate is a GUESS. The certificate's accepting step is unchanged:
    /// substitute the guess into every assertion and require an INDEPENDENT
    /// solver `Unsat` on the negation. `Unsat` there means the substituted
    /// assertion holds in every structure, so where the guess came from is
    /// irrelevant to the theorem — only that it is a CLOSED CONSTANT of exactly
    /// the head's result sort, which the caller re-checks defensively before any
    /// nested solve. A worthless guess costs one refuted combination.
    ///
    /// # The two sources
    ///
    /// 1. SYNTACTIC PINS. A closed constant `k` occurring opposite an
    ///    occurrence of the head in an equality anywhere in the snapshot —
    ///    `(= a 1.5)`, `(= (f 0) (- 2))`. This is what makes the certificate
    ///    able to answer a problem that NAMES its own witness value: the fixed
    ///    `0/1` family can never satisfy `a = 3/2`.
    /// 2. THE EMITTED MODEL, for a NULLARY head only. `I(c) = M(c)` is then not
    ///    an approximation of the model but literally its value, so a grant
    ///    certifies an interpretation the published model already agrees with.
    ///    Restricted to arity 0 on purpose: for a function head the model's
    ///    value at one point says nothing about the constant function `λȳ. c`,
    ///    and pretending otherwise would just burn a combination.
    ///
    /// Both are capped at [`MAX_CONST_INTERP_EXTRA_CANDIDATES`] extras per head
    /// so the combination space stays inside the existing budgets.
    fn const_interp_widened_candidates(
        &mut self,
        snapshot: &[TermId],
        name: &str,
        sort: &Sort,
        arity: usize,
        base: &[TermId],
    ) -> Vec<TermId> {
        let mut out: Vec<TermId> = base.to_vec();
        let mut extras: Vec<TermId> = Vec::new();
        // The head's own nullary occurrence, needed to ask the model for its
        // value. Recovered by WALKING the snapshot for the same reason
        // `const_interp_substitution` does: `mk_var(name, sort)` would mint a
        // different `TermId` that matches nothing.
        let mut nullary_occurrence: Option<TermId> = None;

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = snapshot.to_vec();
        let mut work = MAX_CONST_INTERP_SCAN_WORK;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if work == 0 {
                break;
            }
            work -= 1;
            // Does `t` mention the head at the right arity, at its own node?
            let is_head_occurrence = match self.ctx.terms.get(t) {
                TermData::Var(var_name, _) => arity == 0 && var_name.as_str() == name,
                TermData::App(Symbol::Named(app_name), args) => {
                    app_name.as_str() == name && args.len() == arity
                }
                _ => false,
            };
            if is_head_occurrence && arity == 0 && nullary_occurrence.is_none() {
                nullary_occurrence = Some(t);
            }
            // SYNTACTIC PIN: `(= <head occurrence> <closed const>)`, either way
            // round. Only a literal `Const` node counts — an arbitrary term
            // would not be a closed constant and could not be published.
            if let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(t) {
                if op.as_str() == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    for (occ, konst) in [(a, b), (b, a)] {
                        let occ_is_head = match self.ctx.terms.get(occ) {
                            TermData::Var(var_name, _) => arity == 0 && var_name.as_str() == name,
                            TermData::App(Symbol::Named(app_name), app_args) => {
                                app_name.as_str() == name && app_args.len() == arity
                            }
                            _ => false,
                        };
                        if occ_is_head
                            && matches!(self.ctx.terms.get(konst), TermData::Const(_))
                            && self.ctx.terms.sort(konst) == sort
                            && !out.contains(&konst)
                            && !extras.contains(&konst)
                        {
                            extras.push(konst);
                        }
                    }
                }
            }
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, x, y) => {
                    stack.push(*c);
                    stack.push(*x);
                    stack.push(*y);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }

        // MODEL VALUE (nullary heads only).
        if arity == 0 && extras.len() < MAX_CONST_INTERP_EXTRA_CANDIDATES {
            if let (Some(occurrence), Some(model)) = (nullary_occurrence, self.last_model.clone()) {
                let value = self.evaluate_term(&model, occurrence);
                if let Some(pinned) = self.const_interp_pin_eval_value(sort, &value) {
                    if !out.contains(&pinned) && !extras.contains(&pinned) {
                        extras.push(pinned);
                    }
                }
            }
        }

        extras.truncate(MAX_CONST_INTERP_EXTRA_CANDIDATES);
        out.extend(extras);
        out
    }

    /// Rebuild an evaluated scalar as a closed constant of EXACTLY `sort`.
    ///
    /// Sort-exactness is load-bearing, not tidiness: `EvalValue::Rational`
    /// represents both `Int` and `Real`, and a `Real` constant standing in for
    /// an `Int` head would make the substituted body ill-sorted. Anything the
    /// mapping does not model exactly (uninterpreted-sort elements, sequences,
    /// algebraic reals, `Unknown`) yields `None` — no candidate, no change.
    fn const_interp_pin_eval_value(&mut self, sort: &Sort, value: &EvalValue) -> Option<TermId> {
        match (sort, value) {
            (Sort::Bool, EvalValue::Bool(v)) => Some(self.ctx.terms.mk_bool(*v)),
            (Sort::Int, EvalValue::Rational(v)) if v.is_integer() => {
                Some(self.ctx.terms.mk_int(v.numer().clone()))
            }
            (Sort::Real, EvalValue::Rational(v)) => Some(self.ctx.terms.mk_rational(v.clone())),
            (Sort::BitVec(bv), EvalValue::BitVec { value, width }) if bv.width == *width => {
                Some(self.ctx.terms.mk_bitvec(value.clone(), *width))
            }
            _ => None,
        }
    }

    /// Body of [`Self::try_const_interp_sat_certificate`], split out so the
    /// caller owns the single deadline save/restore.
    fn const_interp_cert_inner(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
        mode: ConstInterpCertMode,
        deadline: ay_core::time::Instant,
        // Which candidate constants each pinned head is enumerated over. See
        // the two-pass note in `try_const_interp_sat_certificate`.
        candidate_source: ConstInterpCandidateSource,
    ) -> Option<()> {
        // ---- 1. PARTITION: every assertion is a top-level `forall` OR a
        //         QUANTIFIER-FREE ground conjunct.
        //
        // The ground conjuncts used to DECLINE, on the grounds that the theorem
        // is stated for an all-`forall` problem and that "a certificate which
        // silently certified only the `forall`s would be proving SAT of a
        // strict SUBSET of the snapshot — a wrong-SAT". That reasoning is
        // exactly right and is preserved: the subset hazard is real, so the
        // widening does NOT skip the ground conjuncts, it DISCHARGES them.
        // Step 5 runs each one through the SAME accepting step as an axiom
        // (substitute `I`, then refute the negation), under the SAME shared
        // interpretation `I`. The certified statement is therefore unchanged in
        // strength — "`I` satisfies EVERY assertion of the snapshot" — and now
        // simply ranges over both kinds of conjunct.
        //
        // The admission test stays purely SYNTACTIC (top-level `Forall`, or a
        // `Bool`-sorted term containing no quantifier) and fail-closed: an
        // assertion that is neither declines the whole certificate.
        if snapshot.is_empty() || snapshot.len() > MAX_CONST_INTERP_ASSERTIONS {
            // SAY SO. This was the certificate's only SILENT decline, and the
            // silence actively misled: the verification-consumer slice family (snapshots of
            // 20 and 24 assertions) is rejected right here, but with no note the
            // only visible symptom was the gate's downstream
            // `deferred-failclosed`, so the family was twice mis-attributed —
            // once to a "constant-only interpretation" limitation and once to a
            // head-count budget. Both are real limits, but they are the SECOND
            // and THIRD gates; this one fires first.
            //
            // Establishing the true chain (assertions -> heads -> "no candidate
            // combination certified every axiom") required making the budgets
            // env-overridable and bisecting, which is work nobody should have to
            // repeat to read a decline.
            const_interp_note(
                mode,
                &format!(
                    "decline: snapshot has {} assertions (empty, or over the \
                     MAX_CONST_INTERP_ASSERTIONS budget of {})",
                    snapshot.len(),
                    MAX_CONST_INTERP_ASSERTIONS
                ),
            );
            return None;
        }

        // ---- 2. SHAPE SCAN: reject out-of-class bodies, collect the
        //         uninterpreted heads.
        struct ConstInterpAxiom {
            body: TermId,
            binders: Vec<(String, Sort)>,
        }
        let mut axioms: Vec<ConstInterpAxiom> = Vec::with_capacity(snapshot.len());
        // Ground conjuncts, discharged under `I` alongside the axioms in step 5.
        let mut grounds: Vec<TermId> = Vec::new();
        // head name -> (result sort, arity). Sort/arity disagreement between
        // two occurrences of one name (an overload) fails closed.
        let mut head_map: HashMap<String, (Sort, usize)> = HashMap::default();
        let mut work = MAX_CONST_INTERP_SCAN_WORK;
        for &q in snapshot {
            // A `no_mbqi` (E-matching-only, Hilbert-choose style) forall must
            // never be discharged by a constructed interpretation.
            if self.ctx.terms.is_no_mbqi(q) {
                return None;
            }
            let TermData::Forall(vars, body, _triggers) = self.ctx.terms.get(q) else {
                // GROUND CONJUNCT. Admitted only when it is `Bool`-sorted and
                // quantifier-free; an `exists` (or a `forall` nested below the
                // top level) is out of class and declines, exactly as it does
                // inside an axiom body.
                if *self.ctx.terms.sort(q) != Sort::Bool || contains_quantifier(&self.ctx.terms, q)
                {
                    const_interp_note(
                        mode,
                        "decline: snapshot contains a non-forall, non-ground-Bool assertion",
                    );
                    return None;
                }
                // Scanned with an EMPTY binder set — a ground conjunct has no
                // binders, so any `Var` it mentions is a free constant. This is
                // load-bearing for soundness, not bookkeeping: it is what makes
                // a head occurring ONLY in a ground conjunct join `head_map`,
                // so `I` pins it too and the sort/arity agreement check covers
                // it. Without it such a head would stay unpinned and its ground
                // conjunct would be discharged against an arbitrary reading.
                self.const_interp_scan_body(q, &HashSet::default(), &mut head_map, &mut work)?;
                grounds.push(q);
                continue;
            };
            let binders: Vec<(String, Sort)> = vars.clone();
            let body = *body;
            if binders.is_empty() || binders.len() > MAX_CONST_INTERP_BINDERS {
                return None;
            }
            if *self.ctx.terms.sort(body) != Sort::Bool {
                return None;
            }
            // Nested `forall` / any `exists` under the body: out of class.
            if contains_quantifier(&self.ctx.terms, body) {
                const_interp_note(mode, "decline: nested quantifier in a forall body");
                return None;
            }
            let binder_names: HashSet<String> =
                binders.iter().map(|(name, _)| name.clone()).collect();
            self.const_interp_scan_body(body, &binder_names, &mut head_map, &mut work)?;
            axioms.push(ConstInterpAxiom { body, binders });
        }
        // At least one `forall`. An all-ground snapshot is the ordinary
        // pipeline's job end-to-end (and its model the gate can check without
        // help); this certificate exists for the quantified case, and keeping
        // the requirement means the widening can never take over a decision
        // that used to be made elsewhere.
        if axioms.is_empty() {
            const_interp_note(mode, "decline: snapshot has no forall assertion");
            return None;
        }

        // ---- 3. CANDIDATE INTERPRETATIONS.
        //
        // A head whose result sort has no closed-constant family is NOT an
        // error: it simply stays uninterpreted, i.e. it is one of the `J`
        // symbols the UNSAT quantifies over. Only heads we actually pin count
        // against the head budget.
        let mut head_list: Vec<(String, Sort, usize)> = head_map
            .into_iter()
            .map(|(name, (sort, arity))| (name, sort, arity))
            .collect();
        // Deterministic order => deterministic combination indices => a
        // reproducible verdict independent of hash iteration order.
        head_list.sort_by(|a, b| a.0.cmp(&b.0));

        /// One head the interpretation actually PINS, with everything needed
        /// both to enumerate it and to publish it as a model entry.
        struct ConstInterpPinnedHead {
            name: String,
            /// Closed constants of the head's result sort, in enumeration order.
            candidates: Vec<TermId>,
            /// Exact positive declaration identity/kind/signature authority.
            binding: ay_frontend::CheckedProjectionBinding,
        }
        let mut interpreted: Vec<ConstInterpPinnedHead> = Vec::new();
        let mut widened_any = false;
        for (name, sort, arity) in head_list {
            let Some(base_candidates) = self.const_interp_candidates(&sort, 0) else {
                continue;
            };
            if base_candidates.is_empty() {
                continue;
            }
            let candidates = match candidate_source {
                ConstInterpCandidateSource::FixedFamily => base_candidates,
                ConstInterpCandidateSource::WithProblemConstants => {
                    let widened = self.const_interp_widened_candidates(
                        snapshot,
                        &name,
                        &sort,
                        arity,
                        &base_candidates,
                    );
                    widened_any |= widened.len() > base_candidates.len();
                    widened
                }
            };
            // Defensive: a candidate whose sort is not EXACTLY the head's
            // result sort would make the rebuilt term ill-sorted. Fail closed.
            // This covers the widened candidates too — a problem-pinned or
            // model-derived constant is checked by the SAME guard as the fixed
            // family, before any nested solve runs.
            if candidates.iter().any(|&c| *self.ctx.terms.sort(c) != sort) {
                return None;
            }
            // ---- 3b. WITNESS SHAPE.
            //
            // A grant on this route publishes `I` itself as the model, so every
            // pinned head must be RENDERABLE as a `(define-fun ...)` under the
            // exact surface name `(get-model)`'s symbol loop visits. A head that
            // is not — an overload signature, a monomorphized parametric
            // instance, a `define-fun`, a solver-internal registration — would
            // otherwise leave a `sat` whose model silently omits the symbol the
            // whole proof is about. Decline the WHOLE certificate: `I` is one
            // structure, and a partially-published `I` is not a witness.
            //
            // Checked HERE, before a single nested solve, so an unpublishable
            // shape costs nothing and can never reach the grant.
            let Some(params) = self.const_interp_witness_shape(&name, &sort, arity) else {
                const_interp_note(
                    mode,
                    &format!("decline: head `{name}` has no printable model entry"),
                );
                return None;
            };
            let request = ay_frontend::ProjectionBindingRequest {
                symbol: Symbol::named(&name),
                parameter_sorts: params.iter().map(|(_, sort)| sort.clone()).collect(),
                result_sort: sort.clone(),
            };
            let binding = self.ctx.check_projection_declaration(&request).ok()?;
            interpreted.push(ConstInterpPinnedHead {
                name,
                candidates,
                binding,
            });
        }
        if interpreted.is_empty() {
            const_interp_note(
                mode,
                "decline: no head has a closed-constant candidate sort",
            );
            return None;
        }
        // Pass 2 exists only to try candidates pass 1 did not have. When the
        // problem named nothing new for any head, pass 2 would re-run exactly
        // the combinations pass 1 already refuted — pure duplicated nested
        // solves against a SHARED wall-clock slice. Decline immediately.
        if matches!(
            candidate_source,
            ConstInterpCandidateSource::WithProblemConstants
        ) && !widened_any
        {
            return None;
        }
        if interpreted.len() > MAX_CONST_INTERP_HEADS {
            const_interp_note(mode, "decline: over the head budget");
            return None;
        }
        let mut combo_count: usize = 1;
        for head in &interpreted {
            combo_count = combo_count.checked_mul(head.candidates.len())?;
        }
        if combo_count == 0 || combo_count > MAX_CONST_INTERP_COMBOS {
            const_interp_note(mode, "decline: over the combination budget");
            return None;
        }

        // ---- 4. FRESH BINDER CONSTANTS, one per binder per axiom.
        //
        // These are the ONLY new symbols the certificate introduces.
        // `mk_fresh_var` appends a monotonic counter AND refuses any spelling
        // already in `TermStore::names`, and the `__ay_` prefix is rejected
        // for user symbols by the frontend, so a fresh constant can alias
        // neither a declared constant, nor a Skolem constant, nor each other.
        // Freshness is exactly what makes `¬B[k̄]` UNSAT mean `∀x̄. B`.
        //
        // Minted ONCE and reused across combinations: each nested solve is an
        // independent problem, so reuse is sound and keeps the arena bounded.
        let mut binder_consts: Vec<HashMap<String, TermId>> = Vec::with_capacity(axioms.len());
        for axiom in &axioms {
            let mut fresh: HashMap<String, TermId> = HashMap::default();
            for (name, sort) in &axiom.binders {
                let k = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("__ay_constinterp!{name}"), sort.clone());
                fresh.insert(name.clone(), k);
            }
            binder_consts.push(fresh);
        }

        // ---- 5. ENUMERATE. Combination 0 is the all-FIRST-candidate
        //         interpretation (all `false` / all `0` / const-`0` arrays),
        //         which is the one that discharges most axiom families.
        let mut solver_calls = 0usize;
        'combos: for combo_ix in 0..combo_count {
            if ay_core::time::Instant::now() >= deadline || self.external_stop_reason().is_some() {
                return None;
            }
            // Mixed-radix decode of `combo_ix` over the per-head candidate
            // lists. One value per head, SHARED by every axiom — that shared
            // `I` is what makes the per-axiom UNSATs compose into a single
            // model of the whole snapshot.
            let mut rest = combo_ix;
            let mut assignment: HashMap<String, TermId> = HashMap::default();
            for head in &interpreted {
                let digit = rest % head.candidates.len();
                rest /= head.candidates.len();
                assignment.insert(head.name.clone(), head.candidates[digit]);
            }

            for (axiom, fresh) in axioms.iter().zip(binder_consts.iter()) {
                let (from, to) = self.const_interp_substitution(axiom.body, fresh, &assignment)?;
                // `from.is_empty()` is legitimate, not an error: neither a
                // binder nor an interpreted head occurs, so the substitution
                // is the identity and the instance IS the body.
                let instance = if from.is_empty() {
                    axiom.body
                } else {
                    self.ctx.terms.substitute(axiom.body, &from, &to)
                };
                // Constant folding in the `mk_*` rebuild path often decides
                // the obligation outright; skip the solver when it did.
                match self.ctx.terms.get(instance) {
                    // The body is a syntactic tautology under `I`. Certified.
                    TermData::Const(Constant::Bool(true)) => continue,
                    // Refuted under `I`; this combination cannot work.
                    TermData::Const(Constant::Bool(false)) => continue 'combos,
                    _ => {}
                }
                if solver_calls >= MAX_CONST_INTERP_SOLVER_CALLS
                    || ay_core::time::Instant::now() >= deadline
                {
                    const_interp_note(mode, "decline: over the nested-solve budget");
                    return None;
                }
                solver_calls += 1;
                // THE ACCEPTING STEP. The checked disposable probe is
                // fail-closed: only a strict-proof-certified `Unsat` token for
                // this exact obligation can discharge the axiom.
                let negated = self.ctx.terms.mk_not(instance);
                let obligation = vec![negated];
                if !self
                    .checked_ground_solve(obligation.clone(), fallback_category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    continue 'combos;
                }
            }

            // GROUND CONJUNCTS, under the SAME `I`. This is the second
            // obligation the all-`forall` partition existed to avoid needing;
            // discharging it here is what keeps the grant a statement about the
            // WHOLE snapshot rather than a subset of it. Identical accepting
            // step to the axioms above (fold to `true`, else refute the
            // negation), identical fail-closed budget, and an empty binder map
            // because a ground conjunct binds nothing.
            for &ground in &grounds {
                let (from, to) =
                    self.const_interp_substitution(ground, &HashMap::default(), &assignment)?;
                let instance = if from.is_empty() {
                    ground
                } else {
                    self.ctx.terms.substitute(ground, &from, &to)
                };
                match self.ctx.terms.get(instance) {
                    // True under `I`. Certified.
                    TermData::Const(Constant::Bool(true)) => continue,
                    // Refuted under `I`; this combination cannot work.
                    TermData::Const(Constant::Bool(false)) => continue 'combos,
                    _ => {}
                }
                if solver_calls >= MAX_CONST_INTERP_SOLVER_CALLS
                    || ay_core::time::Instant::now() >= deadline
                {
                    const_interp_note(mode, "decline: over the nested-solve budget");
                    return None;
                }
                solver_calls += 1;
                let negated = self.ctx.terms.mk_not(instance);
                let obligation = vec![negated];
                if !self
                    .checked_ground_solve(obligation.clone(), fallback_category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    continue 'combos;
                }
            }

            // Every axiom AND every ground conjunct certified under ONE shared
            // interpretation.
            const_interp_note(
                mode,
                &format!(
                    "GRANT: combination {combo_ix}/{combo_count} certifies {} forall assertion(s) \
                     and {} ground conjunct(s) with {solver_calls} nested solve(s)",
                    axioms.len(),
                    grounds.len()
                ),
            );
            return match mode {
                ConstInterpCertMode::On => {
                    // PUBLISH THE WITNESS. `assignment` is `I` — the exact
                    // interpretation every obligation above was discharged
                    // under — so the model entries below are read off the
                    // certified object itself, not reconstructed from it.
                    let witness: Vec<(ay_frontend::CheckedProjectionBinding, TermId)> = interpreted
                        .into_iter()
                        .map(|head| {
                            let value = *assignment.get(head.name.as_str())?;
                            Some((head.binding, value))
                        })
                        .collect::<Option<_>>()?;
                    self.install_const_interp_cert_witness(snapshot, witness, mode)?;
                    Some(())
                }
                // Shadow: run the whole certificate and report, but WITHHOLD
                // the verdict — byte-identical to the gate being off. Nothing
                // is installed either: a shadow run must not touch the model.
                ConstInterpCertMode::Shadow | ConstInterpCertMode::Off => None,
            };
        }
        const_interp_note(
            mode,
            "decline: no candidate combination certified every axiom",
        );
        None
    }

    /// The `(define-fun ...)` PARAMETER LIST for a head the
    /// constant-interpretation certificate is about to pin, or `None` when the
    /// head's interpretation cannot be published as a model entry.
    ///
    /// `(get-model)`'s emitter walks `symbol_iter()` and matches each entry by
    /// its SURFACE name, so an entry keyed by anything else is never printed.
    /// Every filter here exists to guarantee that the entry this certificate
    /// hands over will be found under exactly the spelling the user declared,
    /// with exactly the declared signature:
    ///
    /// - `is_defined_fun`: a `define-fun`'s interpretation is FIXED by the
    ///   problem text and the emitter deliberately omits it; a second
    ///   `define-fun` is a definition conflict for a model validator
    ///   (#mv-defined-fun-emit). (The head scan cannot see one — defined
    ///   applications are macro-expanded at elaboration — so this is belt and
    ///   braces.)
    /// - `is_internal_symbol` / `is_dt_internal_symbol`: not user declarations;
    ///   the emitter suppresses them (#mv-internal-symbol-suppression).
    /// - `overloaded_surface_name`: one surface name with several signatures.
    ///   The certificate pins a core UF IDENTITY; printing it under the shared
    ///   surface name would claim an interpretation for the sibling signatures
    ///   too.
    /// - `internal_name.is_some()`: a monomorphized parametric-datatype member
    ///   or a non-first overload — the term's name is the identity, not the
    ///   surface spelling, so the emitter would never reach this entry.
    /// - signature agreement: the printed `(define-fun)` must have the declared
    ///   arity and the declared result sort, or the model is ill-typed.
    ///
    /// Parameters are named `x!0 ..` (z3's spelling). No capture is possible:
    /// the value this certificate binds is always a CLOSED constant.
    fn const_interp_witness_shape(
        &self,
        name: &str,
        result_sort: &Sort,
        arity: usize,
    ) -> Option<Vec<(String, Sort)>> {
        if self.ctx.is_defined_fun(name)
            || self.ctx.is_internal_symbol(name)
            || self.is_exact_dt_internal_symbol(name)
            || self.ctx.overloaded_surface_name(name).is_some()
        {
            return None;
        }
        let info = self.ctx.symbol_info(name)?;
        if info.internal_name.is_some()
            || info.arg_sorts.len() != arity
            || &info.sort != result_sort
        {
            return None;
        }
        Some(
            info.arg_sorts
                .iter()
                .enumerate()
                .map(|(ix, s)| (format!("x!{ix}"), s.clone()))
                .collect(),
        )
    }

    /// Install a certified interpretation as THE model, replacing any unrelated
    /// raw candidate retained by an earlier solver lane.
    ///
    /// The certificate discharged every assertion after substituting `I`, with
    /// every residual symbol universally free in the refutation query. Thus its
    /// theorem licenses `I ∪ J` for an ARBITRARY `J`; the canonical completion
    /// below is one such `J`. It does *not* license publishing the pre-existing
    /// candidate in place of `I`. Keep an identical parked pair because later
    /// mapper probes may overwrite either `last_model` or the sidecar before the
    /// public SAT funnel runs.
    fn install_const_interp_cert_witness(
        &mut self,
        roots: &[TermId],
        witness: Vec<(ay_frontend::CheckedProjectionBinding, TermId)>,
        mode: ConstInterpCertMode,
    ) -> Option<()> {
        const_interp_note(
            mode,
            &format!(
                "WITNESS: publishing {} model entr{} — {}",
                witness.len(),
                if witness.len() == 1 { "y" } else { "ies" },
                witness
                    .iter()
                    .filter_map(|(binding, _)| {
                        let Symbol::Named(name) = binding.symbol() else {
                            return None;
                        };
                        Some(format!("{}/{}", name, binding.parameter_sorts().len()))
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        );

        // The checked interpretation is semantic model data, not executor
        // routing state. Install it into the exact affine model before any
        // completion or evaluation can observe that model, then extend only
        // declarations proved absent from the exact checked roots. The sole
        // SAT publication funnel later seals this already-final object.
        let mut model = Model::empty();
        // This is also the single shape/type/currentness check for witness
        // values: installation admits only scalar literals and recursively
        // nested const-arrays, stamping every reachable term slot. Keeping the
        // check here avoids a weaker debug-only predicate drifting away from
        // the model's fail-closed production perimeter.
        model.install_certified_const_interps(&self.ctx, witness)?;
        if !self.complete_quantified_output_model_before_seal(&mut model, roots) {
            return None;
        }
        self.const_interp_cert_witness_state = Some(
            ConstInterpWitnessState::pending_for_current_query(self, roots, model)?,
        );
        Some(())
    }

    /// The certified value of `term` under an installed constant-interpretation
    /// witness, if `term` is an occurrence of a head the witness pins.
    ///
    /// `I(f)` is the CONSTANT function `λ ȳ. c_f`, so an application matches
    /// whatever its arguments are, and a 0-ary head matches as a bare `Var`.
    /// Empty (a single `is_empty` test) on every path that has no witness.
    ///
    /// The SORT check is the guard against the engine's name-based binder
    /// convention: a `forall` binder is a `Var` too, and a binder that happened
    /// to share a pinned head's spelling would otherwise be pinned to the head's
    /// value. The certificate already refuses to record a head whose name
    /// shadows a binder, so this is a second line — but a cheap one, and the
    /// failure it prevents (silently evaluating a bound variable as a constant)
    /// is exactly the kind that produces a wrong model with no error.
    pub(in crate::executor) fn const_interp_witness_value(
        &self,
        model: &Model,
        term: TermId,
    ) -> std::result::Result<Option<TermId>, CertifiedConstInterpReadError> {
        let result_sort = self.ctx.terms.sort(term);
        match self.ctx.terms.get(term) {
            TermData::App(symbol, arguments) => model.certified_const_interp_for_application(
                &self.ctx,
                symbol,
                arguments,
                result_sort,
            ),
            TermData::Var(name, _) => model.certified_const_interp_for_application(
                &self.ctx,
                &Symbol::named(name),
                &[],
                result_sort,
            ),
            _ => Ok(None),
        }
    }

    /// The installed constant-interpretation witness entries, for the model
    /// emitter. Empty unless a certificate granted and published `I`.
    pub(in crate::executor) fn const_interp_cert_witness_entries<'a>(
        &self,
        model: &'a Model,
    ) -> &'a [CertifiedConstInterpEntry] {
        self.const_interp_cert_witness_state
            .as_ref()
            .and_then(|state| state.installed_entries_for_output(self, model))
            .unwrap_or(&[])
    }

    /// Shape scan of one `forall` body for the constant-interpretation
    /// certificate: reject anything out of class and record every
    /// uninterpreted head with its result sort and arity.
    ///
    /// Recording a head here is NOT a commitment to interpret it — step 3 of
    /// [`Self::const_interp_cert_inner`] drops the ones with no constant
    /// candidate. It IS a commitment that the scan understood the node.
    fn const_interp_scan_body(
        &self,
        body: TermId,
        binder_names: &HashSet<String>,
        heads: &mut HashMap<String, (Sort, usize)>,
        work: &mut u32,
    ) -> Option<()> {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![body];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if *work == 0 {
                return None;
            }
            *work -= 1;
            match self.ctx.terms.get(t) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    // A `Var` named like a binder IS that binder (the engine's
                    // name-based substitution convention; nested binders are
                    // rejected above, so no other capture is possible).
                    if binder_names.contains(name.as_str()) {
                        continue;
                    }
                    // Otherwise a FREE constant. In AY an uninterpreted
                    // nullary `declare-fun` / `declare-const` elaborates to a
                    // `Var`, NOT a 0-ary `App`, so this is where `(declare-fun
                    // logic_None () Int)` is found.
                    if self.const_interp_head_is_uninterpreted(name, 0) {
                        let sort = self.ctx.terms.sort(t).clone();
                        match heads.get(name.as_str()) {
                            Some((seen_sort, seen_arity)) => {
                                if *seen_sort != sort || *seen_arity != 0 {
                                    return None;
                                }
                            }
                            None => {
                                heads.insert(name.clone(), (sort, 0));
                            }
                        }
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    if let Symbol::Named(name) = sym {
                        if self.const_interp_head_is_uninterpreted(name, args.len()) {
                            let sort = self.ctx.terms.sort(t).clone();
                            match heads.get(name.as_str()) {
                                Some((seen_sort, seen_arity)) => {
                                    if *seen_sort != sort || *seen_arity != args.len() {
                                        return None;
                                    }
                                }
                                None => {
                                    heads.insert(name.clone(), (sort, args.len()));
                                }
                            }
                        } else if const_interp_rebuild_folds_name(name)
                            && self.ctx.symbol_info(name).is_some()
                        {
                            // A USER DECLARATION wearing a builtin spelling.
                            // `+`, `-`, `*`, `and`, `or`, `=`, `to_real`,
                            // `is_int` and friends stay user-declarable, and
                            // `TermStore::rebuild_app` dispatches purely on the
                            // symbol NAME with no check that it IS the builtin.
                            // So once any child under this node changes, the
                            // rebuild would route an uninterpreted user
                            // function through `mk_add` / `mk_and` / ... and
                            // fold it — `(+ 0 1)` to `1` — silently changing
                            // the obligation. Fail closed.
                            return None;
                        }
                    }
                    // Descend regardless: an interpreted operator's arguments
                    // and an uninterpreted head's arguments can both contain
                    // further heads that occur elsewhere at top level.
                    stack.extend(args.iter().copied());
                }
                // `Let`, `Forall`, `Exists`, and any FUTURE `TermData` variant
                // could hide a binder occurrence or a quantifier. Fail closed.
                _ => return None,
            }
        }
        Some(())
    }

    /// Is `name` — applied at exactly `arity` arguments — a genuinely
    /// UNINTERPRETED, user-declared symbol whose interpretation this
    /// certificate is free to choose?
    ///
    /// This is the guard that keeps the certificate honest. Fabricating an
    /// interpretation for a symbol whose semantics is PINNED (`+`, `mod`,
    /// `select`, `bvadd`, a datatype constructor/selector/tester) would make
    /// the nested UNSAT prove nothing about the original body — a wrong-SAT.
    /// So the test is a conjunction of negative filters AND a POSITIVE
    /// requirement that the frontend really holds a declaration of this name
    /// at this arity.
    fn const_interp_head_is_uninterpreted(&self, name: &str, arity: usize) -> bool {
        // Negative: every interpreted family the engine knows about.
        if is_pure_arith_bool_symbol(name)
            || is_finite_table_interpreted_symbol(name)
            || is_interpreted_bv_symbol(name)
            || !is_mbqi_completable_uf_symbol(name)
        {
            return false;
        }
        // Negative: reserved operator / reserved symbol spellings. A user
        // declaration can never own one of these, so anything that reaches
        // here bearing such a name is a builtin.
        if ay_frontend::is_reserved_op_name(name) || ay_frontend::is_reserved_symbol(name) {
            return false;
        }
        // Negative: datatype constructors, selectors and testers are
        // structurally interpreted, not free.
        if self.ctx.is_datatype_member_name(name)
            || self.symbol_is_datatype_selector_or_constructor(name)
        {
            return false;
        }
        // Negative: solver-invented internal constants (the eager
        // single-constructor datatype-elimination field constants). They are
        // not user declarations and carry structural obligations elsewhere.
        if self.ctx.is_internal_symbol(name) {
            return false;
        }
        // POSITIVE: the frontend must hold a declaration for exactly this
        // identity at exactly this arity. `symbol_info_by_identity` resolves
        // private overload / parametric-instance identities; `symbol_info` is
        // the plain surface lookup.
        let info = self
            .ctx
            .symbol_info_by_identity(name)
            .or_else(|| self.ctx.symbol_info(name));
        match info {
            Some(info) => info.arg_sorts.len() == arity,
            None => false,
        }
    }

    /// Closed constant candidates for a head of result sort `sort`, or `None`
    /// when the sort has no constant family the certificate will use (in which
    /// case the head is left uninterpreted, which is always sound).
    ///
    /// Deliberately tiny. Every extra candidate multiplies the combination
    /// count, and the enumeration is capped — a wider family would DECLINE
    /// more often, not grant more often.
    fn const_interp_candidates(&mut self, sort: &Sort, depth: u32) -> Option<Vec<TermId>> {
        if depth > CONST_INTERP_SORT_DEPTH {
            return None;
        }
        match sort {
            // Both polarities are required: `∀v. ¬contains(empty, v)` needs
            // `false` and `∀s,p,x. contains(push(s,p),x) = (p=x ∨ contains(s,x))`
            // needs `true`.
            Sort::Bool => Some(vec![
                self.ctx.terms.mk_bool(false),
                self.ctx.terms.mk_bool(true),
            ]),
            // `0` is the workhorse; `1` is needed both as a nonzero `mod`/`div`
            // divisor and to separate two heads a disequality forces apart.
            Sort::Int => Some(vec![
                self.ctx.terms.mk_int(num_bigint::BigInt::from(0)),
                self.ctx.terms.mk_int(num_bigint::BigInt::from(1)),
            ]),
            Sort::Real => Some(vec![
                self.ctx
                    .terms
                    .mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(0))),
                self.ctx
                    .terms
                    .mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(1))),
            ]),
            // Exactly ONE array candidate — the constant array over the
            // element sort's FIRST candidate. `select` of it folds to that
            // value at every index, which is what discharges the
            // array/sequence "bridge" axiom family.
            Sort::Array(array) => {
                let element = self.const_interp_candidates(&array.element_sort, depth + 1)?;
                let &first = element.first()?;
                Some(vec![self
                    .ctx
                    .terms
                    .mk_const_array(array.index_sort.clone(), first)])
            }
            // Uninterpreted sorts, sequences, datatypes, bitvectors, strings,
            // floats: no candidate. The head stays FREE, which is sound — the
            // nested UNSAT quantifies over every interpretation of it.
            _ => None,
        }
    }

    /// Build the SIMULTANEOUS substitution that turns a `forall` body into its
    /// certificate obligation. THIS IS THE ONE SOUNDNESS-CRITICAL STEP, so it
    /// is spelled out node by node.
    ///
    /// Returns `(from, to)` for [`ay_core::TermStore::substitute`], which
    /// matches by `TermId` and — crucially — returns `to[i]` for a node equal
    /// to `from[i]` WITHOUT recursing into it. Two kinds of pair are emitted:
    ///
    /// 1. `f(t̄) ↦ c_f` for every application node whose head `f` is in the
    ///    interpretation. The WHOLE application is replaced, and the arguments
    ///    are deliberately NOT visited: `I(f)` is the constant function
    ///    `λ ȳ. c_f`, so `f(anything)` is `c_f` whatever `anything` is — even
    ///    if it mentions the binder, another interpreted head, or `f` itself.
    ///    `substitute`'s no-recurse-on-hit rule makes the rebuild agree with
    ///    that reading exactly.
    /// 2. `x ↦ k_x` for every occurrence of a binder, where `k_x` is the
    ///    axiom's fresh constant. This is the Skolem/Herbrand step: `¬B[k̄]`
    ///    UNSAT with `k̄` fresh is precisely `∀x̄. B` valid.
    ///
    /// Binder occurrences are recovered by WALKING THE BODY, not by rebuilding
    /// a `Var` from the binder's name and sort: the frontend mints binders
    /// with `mk_fresh_var`, which never registers the spelling in
    /// `TermStore::names`, so `mk_var(name, sort)` would mint a DIFFERENT
    /// `Var(name, counter)` with a different `TermId`, match nothing, and
    /// silently return the body unchanged — a wrong answer that looks like a
    /// successful identity substitution.
    ///
    /// The two pair kinds cannot collide: a node is classified once, and the
    /// scan already refused to record a head whose name shadows a binder.
    /// `from` is deduplicated by the `seen` set (each `TermId` is pushed at
    /// most once), which matters because `substitute` linearly scans `from` at
    /// every node.
    fn const_interp_substitution(
        &self,
        body: TermId,
        binder_consts: &HashMap<String, TermId>,
        assignment: &HashMap<String, TermId>,
    ) -> Option<(Vec<TermId>, Vec<TermId>)> {
        let mut from: Vec<TermId> = Vec::new();
        let mut to: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![body];
        let mut work = MAX_CONST_INTERP_SCAN_WORK;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if work == 0 {
                return None;
            }
            work -= 1;
            match self.ctx.terms.get(t) {
                TermData::Const(_) => {}
                TermData::Var(name, _) => {
                    if let Some(&k) = binder_consts.get(name.as_str()) {
                        // Pair kind 2: binder occurrence -> fresh constant.
                        from.push(t);
                        to.push(k);
                    } else if let Some(&value) = assignment.get(name.as_str()) {
                        // Pair kind 1, nullary case: an uninterpreted constant
                        // is a `Var` in AY, and `I` pins it to `value`.
                        from.push(t);
                        to.push(value);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(sym, args) => {
                    if let Symbol::Named(name) = sym {
                        if let Some(&value) = assignment.get(name.as_str()) {
                            // Pair kind 1: whole application -> constant, and
                            // do NOT descend into the arguments (see above).
                            from.push(t);
                            to.push(value);
                            continue;
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                // Same fail-closed perimeter as the scan. Unreachable in
                // practice (the scan already rejected these shapes) but the
                // walk must never silently skip a node that could contain a
                // binder occurrence.
                _ => return None,
            }
        }
        Some((from, to))
    }
}

/// One G-route (ground-reduction) forall: `forall var_names. t = ctor(vars) =>
/// phi`, with `t` GROUND. DT injectivity pins the binders at `(sel_i t)`.
struct GCertInfo {
    /// The ground term whose constructor shape the guard tests.
    t: TermId,
    /// The guard's constructor name.
    ctor: String,
    /// The consequent (the non-guard disjunct).
    phi: TermId,
    /// The bound variable names, in constructor-field order.
    var_names: Vec<String>,
}

/// Exact value domain of the finite-table certificate evaluator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::executor) enum TableCertVal {
    /// Integer value (arbitrary precision — no overflow surface).
    Int(num_bigint::BigInt),
    /// Exact rational value (Real codomain; no rounding surface).
    Rat(num_rational::BigRational),
    /// Boolean value.
    Bool(bool),
}

/// Key of one finite-table entry: `(ground-prefix value vector, trailing
/// point)`. The prefix is EMPTY for the classic unary `f(x)` table and
/// non-empty for a curried `f(g1..gn, x)` table (CCMC M1, `g1..gn` binder-free
/// and Int/Real-valued). Keys are VALUE vectors (evaluated under the candidate
/// model), NOT syntactic prefixes, so coincident prefixes (`a = b` in the
/// model) share ONE row — a disagreement there is a detected row conflict, not
/// two disjoint tables that each pass vacuously.
type TableCertKey = (Vec<num_rational::BigRational>, num_rational::BigRational);

/// Codomain kind of a finite-table symbol (the certified fragment's three
/// admissible sorts). The binder DOMAIN is `Int` or `Real` — see the
/// Real-binder section on [`Executor::try_finite_table_sat_certificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum TableCertSort {
    /// Int codomain (`TableCertVal::Int` values).
    Int,
    /// Real codomain (`TableCertVal::Rat` values).
    Real,
    /// Bool codomain (`TableCertVal::Bool` values).
    Bool,
}

/// Budget: maximum table points (union across all table symbols) the
/// finite-table certificate will check pointwise.
const MAX_TABLE_CERT_POINTS_TOTAL: usize = 64;
/// Budget: maximum default-vector combinations enumerated.
const MAX_TABLE_CERT_DEFAULT_COMBOS: usize = 16;
/// Budget: maximum default candidates per table symbol.
const MAX_TABLE_CERT_DEFAULTS_PER_SYM: usize = 6;
/// Budget: maximum isolated ground solver calls for residual certificates.
const MAX_TABLE_CERT_SOLVER_CALLS: usize = 6;

/// Interpreted operators admitted inside a finite-table-certified body. The
/// exact evaluator implements precisely this set over BigInt/BigRational/Bool;
/// everything else (div/mod/abs, theory symbols, ...) is out of class.
/// `/` is additionally admitted by the scan, but ONLY with literal nonzero
/// numeral divisors (checked at the scan site, not here — do not add it).
/// `true` iff `sort` IS or structurally CONTAINS one of the named
/// uninterpreted sorts (array index/element, sequence element, datatype —
/// datatypes are conservatively `true` since their fields may mention the
/// sort). Used by the empty-universe singleton decide to refuse any snapshot
/// where a composite sort could smuggle domain elements past the
/// ground-universe scan.
fn sort_mentions_uninterpreted_names(sort: &Sort, names: &HashSet<String>) -> bool {
    match sort {
        Sort::Uninterpreted(n) | Sort::TypeVar(n) => names.contains(n),
        Sort::Array(a) => {
            sort_mentions_uninterpreted_names(&a.index_sort, names)
                || sort_mentions_uninterpreted_names(&a.element_sort, names)
        }
        Sort::Seq(e) => sort_mentions_uninterpreted_names(e, names),
        // Conservative: a datatype's constructor fields may mention the sort.
        Sort::Datatype(_) => !names.is_empty(),
        _ => false,
    }
}

fn is_finite_table_interpreted_symbol(name: &str) -> bool {
    matches!(
        name,
        "and"
            | "or"
            | "not"
            | "=>"
            | "xor"
            | "ite"
            | "="
            | "distinct"
            | "<"
            | "<="
            | ">"
            | ">="
            | "+"
            | "-"
            | "*"
            | "to_real"
    )
}

/// Maximum concrete Int refutation-witness candidates synthesized by
/// [`synthesize_int_refutation_candidates`]. Callers additionally cap the
/// number of isolated solves they run and share a tight deadline, so this
/// bounds list construction, not solve time.
pub(in crate::executor) const MAX_INT_REFUTATION_CANDIDATES: usize = 24;

/// Synthesize concrete `Int` WITNESS candidates `c` for refuting a universally
/// quantified assertion `forall x. B(x)` at a ground point: if any standalone
/// `B(c)` is UNSAT, the universal (and with it a conjunctive-position problem)
/// is refuted. Shared by the bounded quantified-lemma decider's UNSAT leg and
/// the per-candidate isolated-instance pass of
/// `disambiguate_cegqi_valid_via_mbqi_inner` (the sibling of
/// `synthesize_mbqi_candidates`, which synthesizes from the model instead).
///
/// Candidate sources, in priority order:
/// 1. Residue-guided values for power shapes: when `body` contains an equality
///    atom with one side a syntactic SQUARE (`(* t t)` with identical factor
///    terms), the small quadratic non-residues 2, 3, 5, 6, 7 witness the
///    falsity of "every value is a perfect square"-style universals.
/// 2. A small constant window ordered by magnitude (0, 1, -1, …, 8, -8).
/// 3. Ground integer constants appearing in `snapshot`, each with ±1/±2
///    offsets.
///
/// Candidate synthesis is NOT a soundness surface: every candidate is verified
/// by an isolated ground solve at the caller and silently skipped otherwise —
/// the trusted base is the ground solver's UNSAT, never the heuristic.
pub(in crate::executor) fn synthesize_int_refutation_candidates(
    terms: &ay_core::TermStore,
    body: TermId,
    snapshot: &[TermId],
) -> Vec<num_bigint::BigInt> {
    use num_bigint::BigInt;
    let mut out: Vec<BigInt> = Vec::new();
    let mut seen: HashSet<BigInt> = HashSet::default();
    let push = |out: &mut Vec<BigInt>, seen: &mut HashSet<BigInt>, v: BigInt| {
        if out.len() < MAX_INT_REFUTATION_CANDIDATES && seen.insert(v.clone()) {
            out.push(v);
        }
    };

    // 1. Residue-guided candidates for square shapes.
    if body_has_syntactic_square_equality(terms, body) {
        for c in [2i64, 3, 5, 6, 7] {
            push(&mut out, &mut seen, BigInt::from(c));
        }
    }

    // 2. Small window ordered by magnitude.
    push(&mut out, &mut seen, BigInt::ZERO);
    for c in 1i64..=8 {
        push(&mut out, &mut seen, BigInt::from(c));
        push(&mut out, &mut seen, BigInt::from(-c));
    }

    // 3. Snapshot ground Int constants ± {0, 1, 2}.
    let mut ground_consts: Vec<BigInt> = Vec::new();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = snapshot.to_vec();
    while let Some(t) = stack.pop() {
        if ground_consts.len() >= 4 {
            break;
        }
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Const(Constant::Int(v)) => {
                if !ground_consts.contains(v) {
                    ground_consts.push(v.clone());
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
    for g in ground_consts {
        for k in [0i64, 1, -1, 2, -2] {
            push(&mut out, &mut seen, g.clone() + BigInt::from(k));
        }
    }

    out
}

/// True when `body` contains an equality atom one of whose sides is a
/// syntactic square `(* t t)` (identical factor `TermId`s) — the power shape
/// that makes the quadratic non-residues high-value refutation candidates.
fn body_has_syntactic_square_equality(terms: &ay_core::TermStore, body: TermId) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(sym, args) => {
                if sym.name() == "=" && args.len() == 2 {
                    let is_square = |side: TermId| match terms.get(side) {
                        TermData::App(mul, margs) => {
                            mul.name() == "*" && margs.len() == 2 && margs[0] == margs[1]
                        }
                        _ => false,
                    };
                    if is_square(args[0]) || is_square(args[1]) {
                        return true;
                    }
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
    false
}

pub(in crate::executor) fn is_mbqi_completable_uf_symbol(name: &str) -> bool {
    !matches!(
        name,
        "=" | "distinct"
            | "and"
            | "or"
            | "not"
            | "=>"
            | "ite"
            | "+"
            | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "<"
            | "<="
            | ">"
            | ">="
            | "select"
            | "store"
            | "const-array"
    ) && !name.starts_with("bv")
        && !name.starts_with("str.")
        && !name.starts_with("seq.")
        && !name.starts_with("fp.")
        && !name.starts_with("re.")
}

/// True when `name` is a builtin arithmetic or boolean operator (LIA/LRA/Bool
/// core). Used by `body_is_pure_arith_bool` to decide whether a `forall` body
/// contains any uninterpreted/theory application that UF completion could
/// complete; anything not in this set (a UF, array, datatype, seq, string, or
/// FP symbol) makes the body non-pure and leaves the completion check intact.
/// The subset of [`is_pure_arith_bool_symbol`] operators whose value ay's model
/// evaluator pins EXACTLY over Int: linear arithmetic (`+ -`), the order/eq
/// relations, and the Bool connectives. EXCLUDES `* / div mod abs to_real to_int
/// is_int` — the nonlinear / Euclidean / conversion operators behind the #8969
/// popcount wrong-SAT (model validation falls back on unevaluable atoms).
fn is_evaluable_linear_symbol(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "="
            | "distinct"
            | "<"
            | "<="
            | ">"
            | ">="
            | "and"
            | "or"
            | "not"
            | "=>"
            | "xor"
            | "ite"
            | "true"
            | "false"
    )
}

pub(in crate::executor) fn is_pure_arith_bool_symbol(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "abs"
            | "="
            | "distinct"
            | "<"
            | "<="
            | ">"
            | ">="
            | "and"
            | "or"
            | "not"
            | "=>"
            | "xor"
            | "ite"
            | "to_real"
            | "to_int"
            | "is_int"
            | "true"
            | "false"
    )
}

/// True when `name` is an interpreted BitVector operator (closed-form theory
/// function). The frontend's reserved-operator table supplies declaration
/// identity for the `bv*` family: a user UF such as `bvtrap` must not become an
/// interpreted operator merely because its spelling shares that prefix.
///
/// Kept separate from `is_pure_arith_bool_symbol` because the callers use this
/// narrower classification for BV evaluation, UF-adoption, and conservative
/// certificate gates.
fn is_interpreted_bv_symbol(name: &str) -> bool {
    (name.starts_with("bv") && ay_frontend::is_reserved_op_name(name))
        || matches!(
            name,
            "concat"
                | "extract"
                | "zero_extend"
                | "sign_extend"
                | "rotate_left"
                | "rotate_right"
                | "repeat"
                | "nat2bv"
                | "int2bv"
                | "ubv_to_int"
                | "sbv_to_int"
                | "int_to_bv"
        )
}

fn is_quantifier_consumer_completable_bool_predicate(name: &str) -> bool {
    name == "logic_good__bucket"
        || name == "logic_no_double_binding"
        || name == "logic_no__double__binding"
        || name.starts_with("logic_good__bucket__placeholder_")
        || name.starts_with("logic_no_double_binding__placeholder_")
        || name.starts_with("logic_no__double__binding__placeholder_")
        || name.starts_with("method_good_bucket_")
        || name.starts_with("method_no_double_binding_")
}

fn is_quantifier_consumer_completion_arith_uf_symbol(name: &str) -> bool {
    name.starts_with("__quantifier_consumer")
        || name.starts_with("__seq_")
        || name.starts_with("seq_")
        || name.starts_with("logic_")
        || name.starts_with("method_")
}

fn is_mbqi_constant_value_symbol(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "*"
            | "div"
            | "mod"
            | "abs"
            | "to_real"
            | "bv2nat"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnot"
            | "bvneg"
            | "concat"
            | "extract"
            | "zero_extend"
            | "sign_extend"
            | "int2bv"
            | "const-array"
            | "select"
    )
}

fn same_pair(a: TermId, b: TermId, lhs: TermId, rhs: TermId) -> bool {
    (a == lhs && b == rhs) || (a == rhs && b == lhs)
}

#[cfg(test)]
mod skipped_quantifier_gate_tests {
    use super::*;
    use ay_frontend::parse;

    fn executor_for(input: &str) -> Executor {
        let commands = parse(input).expect("test script parses");
        let mut executor = Executor::new();
        executor
            .execute_all(&commands)
            .expect("test script elaborates");
        executor
    }

    fn declared_identity_quant(executor: &mut Executor, name: &str, sort: Sort) -> TermId {
        let info = executor
            .ctx
            .symbol_info(name)
            .expect("declared identity symbol");
        let identity = executor.ctx.symbol_identity_name(name, info).to_string();
        let variable = executor.ctx.terms.mk_fresh_var("x", sort.clone());
        let TermData::Var(variable_name, _) = executor.ctx.terms.get(variable) else {
            panic!("fresh binder is a variable")
        };
        let variable_name = variable_name.clone();
        let application =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named(identity), [variable], sort.clone());
        let body = executor.ctx.terms.mk_eq(application, variable);
        executor
            .ctx
            .terms
            .mk_forall(vec![(variable_name, sort)], body)
    }

    fn checked_binding(
        executor: &Executor,
        name: &str,
        parameter_sorts: Vec<Sort>,
        result_sort: Sort,
    ) -> ay_frontend::CheckedProjectionBinding {
        let info = executor
            .ctx
            .symbol_info(name)
            .expect("declared ordinary symbol");
        let identity = executor.ctx.symbol_identity_name(name, info).to_string();
        executor
            .ctx
            .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
                symbol: Symbol::named(identity),
                parameter_sorts,
                result_sort,
            })
            .expect("ordinary declaration binds positively")
    }

    fn checked_nullary_binding(
        executor: &Executor,
        name: &str,
        result_sort: Sort,
    ) -> ay_frontend::CheckedProjectionBinding {
        checked_binding(executor, name, Vec::new(), result_sort)
    }

    #[test]
    fn const_interp_pending_rejects_value_slot_reuse_but_accepts_append_only_growth() {
        let mut executor = executor_for("(set-logic ALL) (declare-const c Int)");
        let root = executor.ctx.terms.true_term();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let value = executor.ctx.terms.mk_int(num_bigint::BigInt::from(37_919));
        let mut model = Model::empty();
        model
            .install_certified_const_interps(
                &executor.ctx,
                vec![(checked_nullary_binding(&executor, "c", Sort::Int), value)],
            )
            .expect("closed, correctly sorted value");
        let state = ConstInterpWitnessState::pending_for_current_query(&executor, &[root], model)
            .expect("live constant-interpretation package");

        let _suffix = executor
            .ctx
            .terms
            .mk_fresh_var("const-package-suffix", Sort::Bool);
        assert!(state.is_pending_current_for(&executor, &[root]));

        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor.ctx.terms.mk_int(num_bigint::BigInt::from(37_920));
        assert_eq!(replacement, value, "rollback should reuse the numeric slot");
        assert!(
            !state.is_pending_current_for(&executor, &[root]),
            "a stale witness value cannot be retargeted by numeric TermId reuse"
        );
    }

    #[test]
    fn const_interp_entry_rejects_wrong_sort_and_nonconstant_value() {
        let mut executor = executor_for("(set-logic ALL) (declare-const c Int)");
        let false_term = executor.ctx.terms.false_term();
        let mut wrong_sort = Model::empty();
        assert!(wrong_sort
            .install_certified_const_interps(
                &executor.ctx,
                vec![(
                    checked_nullary_binding(&executor, "c", Sort::Int),
                    false_term,
                )],
            )
            .is_none());

        let scoped = executor.ctx.terms.mk_fresh_var("scoped", Sort::Int);
        let mut nonconstant = Model::empty();
        assert!(nonconstant
            .install_certified_const_interps(
                &executor.ctx,
                vec![(checked_nullary_binding(&executor, "c", Sort::Int), scoped,)],
            )
            .is_none());

        let one = executor.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let expression = executor
            .ctx
            .terms
            .mk_app(Symbol::named("+"), [one, one], Sort::Int);
        let mut closed_expression = Model::empty();
        assert!(closed_expression
            .install_certified_const_interps(
                &executor.ctx,
                vec![(
                    checked_nullary_binding(&executor, "c", Sort::Int),
                    expression,
                )],
            )
            .is_none());
    }

    #[test]
    fn const_interp_entry_accepts_only_exact_nested_const_array_value_graphs() {
        let nested_sort = Sort::array(Sort::Int, Sort::array(Sort::Bool, Sort::Int));
        let mut executor = executor_for(
            "(set-logic ALL)
             (declare-const a (Array Int (Array Bool Int)))",
        );
        let zero = executor.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let inner = executor.ctx.terms.mk_const_array(Sort::Bool, zero);
        let outer = executor.ctx.terms.mk_const_array(Sort::Int, inner);

        let mut exact = Model::empty();
        exact
            .install_certified_const_interps(
                &executor.ctx,
                vec![(
                    checked_nullary_binding(&executor, "a", nested_sort.clone()),
                    outer,
                )],
            )
            .expect("recursively nested const-array is a closed exact value");
        assert!(exact.certified_const_interps_are_current(&executor.ctx));
        assert_eq!(exact.certified_const_interp_entries()[0].value(), outer);

        let malformed =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("const-array"), [zero], nested_sort.clone());
        let mut wrong_child_sort = Model::empty();
        assert!(wrong_child_sort
            .install_certified_const_interps(
                &executor.ctx,
                vec![(
                    checked_nullary_binding(&executor, "a", nested_sort),
                    malformed,
                )],
            )
            .is_none());
    }

    #[test]
    fn const_interp_semantics_are_model_owned_clone_visible_and_foreign_isolated() {
        let mut executor = executor_for(
            "(set-logic ALL)
             (declare-fun f (Int) Bool)
             (declare-const c Int)",
        );
        let true_term = executor.ctx.terms.true_term();
        let forty_two = executor.ctx.terms.mk_int(num_bigint::BigInt::from(42));
        let c = executor
            .ctx
            .symbol_info("c")
            .and_then(|info| info.term)
            .expect("declared constant term");

        let mut exact = Model::empty();
        exact
            .install_certified_const_interps(
                &executor.ctx,
                vec![
                    (
                        checked_binding(&executor, "f", vec![Sort::Int], Sort::Bool),
                        true_term,
                    ),
                    (
                        checked_nullary_binding(&executor, "c", Sort::Int),
                        forty_two,
                    ),
                ],
            )
            .expect("both exact constant interpretations install atomically");
        assert!(exact.euf_model.is_none());
        assert!(!exact.completed_values.contains_key(&c));

        let epoch = exact.seal_quantified_grant_model();
        let cloned = exact.clone();
        assert!(exact.carries_quantified_grant_model(&epoch));
        assert!(
            !cloned.carries_quantified_grant_model(&epoch),
            "semantic clones share immutable entries but never publication authority"
        );

        let three = executor.ctx.terms.mk_int(num_bigint::BigInt::from(3));
        let f_three = executor
            .ctx
            .terms
            .mk_app(Symbol::named("f"), [three], Sort::Bool);

        // Deliberately install an unrelated ambient model. Evaluation must use
        // the model argument, not `Executor::last_model` pointer identity or a
        // producer-owned sidecar.
        executor.last_model = Some(Model::empty());
        assert_eq!(
            executor.evaluate_term(&exact, f_three),
            EvalValue::Bool(true)
        );
        assert_eq!(
            executor.evaluate_term(&cloned, f_three),
            EvalValue::Bool(true)
        );
        assert_eq!(
            executor.evaluate_term(&cloned, c),
            EvalValue::Rational(num_rational::BigRational::from_integer(
                num_bigint::BigInt::from(42)
            ))
        );
        assert_eq!(
            executor.evaluate_term(
                executor.last_model.as_ref().expect("foreign ambient model"),
                f_three,
            ),
            EvalValue::Unknown,
            "a foreign model cannot observe another model's certified package"
        );
    }

    #[test]
    fn const_interp_model_rejects_popped_identical_declaration() {
        let mut executor = executor_for(
            "(set-logic ALL)
             (push 1)
             (declare-const c Int)",
        );
        let value = executor.ctx.terms.mk_int(num_bigint::BigInt::from(7));
        let mut model = Model::empty();
        model
            .install_certified_const_interps(
                &executor.ctx,
                vec![(checked_nullary_binding(&executor, "c", Sort::Int), value)],
            )
            .expect("scoped declaration is initially current");
        assert!(model.certified_const_interps_are_current(&executor.ctx));

        let replacement = parse(
            "(pop 1)
             (declare-const c Int)",
        )
        .expect("replacement declaration parses");
        executor
            .execute_all(&replacement)
            .expect("scope pop and identical redeclaration elaborate");
        let replacement_c = executor
            .ctx
            .symbol_info("c")
            .and_then(|info| info.term)
            .expect("replacement constant term");
        let TermData::Var(replacement_identity, _) = executor.ctx.terms.get(replacement_c) else {
            panic!("replacement constant is a variable")
        };
        assert_ne!(
            model.certified_const_interp_entries()[0].symbol(),
            &Symbol::named(replacement_identity),
            "the regression must exercise a fresh core identity that misses the old exact-symbol key"
        );

        assert!(!model.certified_const_interps_are_current(&executor.ctx));
        assert!(matches!(
            model.certified_const_interp_for_application(
                &executor.ctx,
                &Symbol::named(replacement_identity),
                &[],
                &Sort::Int,
            ),
            Err(CertifiedConstInterpReadError::StaleIdentity)
        ));
        assert_eq!(
            executor.evaluate_term(&model, replacement_c),
            EvalValue::Unknown,
            "same spelling and signature cannot retarget stale declaration authority"
        );
    }

    #[test]
    fn left_inverse_certificate_rejects_undeclared_raw_identity_head() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("x", Sort::Bool);
        let identity_x = executor
            .ctx
            .terms
            .mk_app(Symbol::named("identity"), vec![x], Sort::Bool);
        let body = executor.ctx.terms.mk_eq(identity_x, x);
        let quant = executor
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Bool)], body);
        executor.ctx.assertions.push(quant);
        let roots = executor.ctx.assertions.clone();

        assert!(
            executor
                .mbqi_sat_validated_left_inverse_axioms(&roots, &[quant], Model::empty())
                .is_none(),
            "a raw core spelling is not positive authority for a free UF declaration"
        );
    }

    #[test]
    fn finite_table_shared_symbol_package_covers_the_complete_root_window() {
        let mut executor = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (declare-fun g (Int) Int)
             (assert (forall ((x Int)) (>= (f x) 0)))
             (assert (forall ((y Int)) (>= (+ (f y) (g y)) 0)))
             (assert (= (f 2) 3))
             (assert (= (g 2) 0))",
        );
        let roots = executor.ctx.assertions.clone();

        assert!(
            executor
                .try_finite_table_sat_certificate(&roots, LogicCategory::Uflia)
                .is_some(),
            "one shared interpretation must certify both foralls and both ground pins"
        );
        assert!(
            executor
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_pending_current_for(&executor, &roots)),
            "the parked model must authenticate the complete ordered root window"
        );
    }

    #[test]
    fn left_inverse_certificate_installs_and_seals_checked_model_a_not_ambient_model_b() {
        let mut executor = executor_for(
            "(set-logic ALL)
             (declare-fun identity (Int) Int)",
        );
        let quant = declared_identity_quant(&mut executor, "identity", Sort::Int);
        executor.ctx.assertions.push(quant);
        let roots = executor.ctx.assertions.clone();
        let marker = executor.ctx.terms.mk_var("model_marker", Sort::Bool);
        let mut model_a = Model::empty();
        model_a
            .completed_values
            .insert(marker, EvalValue::Bool(true));
        let mut model_b = Model::empty();
        model_b
            .completed_values
            .insert(marker, EvalValue::Bool(false));
        executor.last_model = Some(model_b);

        let evidence = executor
            .mbqi_sat_validated_left_inverse_axioms(&roots, &[quant], model_a)
            .expect("the unary identity theorem certifies model A");
        assert!(
            executor.install_mbqi_sat_authority(evidence),
            "authority must be sealed against the model object the theorem checked"
        );
        let installed = executor
            .last_model
            .as_ref()
            .expect("the checked source model is installed");
        assert_eq!(
            executor.evaluate_term(installed, marker),
            EvalValue::Bool(true),
            "ambient model B must not be sealed or retained after checking model A"
        );
    }

    #[test]
    fn left_inverse_certificate_rejects_popped_identical_redeclaration() {
        let mut executor = executor_for(
            "(set-logic ALL)
             (push 1)
             (declare-fun identity (Int) Int)",
        );
        let stale_quant = declared_identity_quant(&mut executor, "identity", Sort::Int);
        executor.ctx.assertions.push(stale_quant);
        let stale_roots = executor.ctx.assertions.clone();

        let replacement = parse(
            "(pop 1)
             (declare-fun identity (Int) Int)",
        )
        .expect("replacement declaration parses");
        executor
            .execute_all(&replacement)
            .expect("scope pop and identical redeclaration elaborate");

        assert!(
            executor
                .mbqi_sat_validated_left_inverse_axioms(
                    &stale_roots,
                    &[stale_quant],
                    Model::empty(),
                )
                .is_none(),
            "a new declaration with the same spelling and signature must not authorize stale roots"
        );
    }

    #[test]
    fn left_inverse_certificate_rejects_fixed_datatype_constructor_identity() {
        let mut executor = executor_for(
            "(set-logic ALL)
             (declare-datatype Nat ((zero) (succ (pred Nat))))
             (assert (forall ((x Nat)) (= (succ x) x)))",
        );
        let roots = executor.ctx.assertions.clone();
        let [quant] = roots.as_slice() else {
            panic!("one datatype identity axiom")
        };
        let quant = *quant;

        assert!(
            executor
                .mbqi_sat_validated_left_inverse_axioms(&roots, &[quant], Model::empty())
                .is_none(),
            "a fixed datatype constructor must never be reinterpreted as a free identity UF"
        );
    }

    #[test]
    fn left_inverse_delegates_the_native_indexed_bv_family() {
        let mut executor = Executor::new();
        let extract = Symbol::indexed("extract", vec![3, 2]);
        let declared = HashSet::default();

        assert!(Executor::left_inverse_application_is_native(&extract));
        assert!(executor.li_symbol_is_delegable_interpreted(&extract, &declared));

        // Build a raw indexed application so this test exercises the
        // left-inverse re-evaluator's rebuild/delegation path rather than a
        // TermStore constructor folding the constant expression first.
        let input = executor
            .ctx
            .terms
            .mk_bitvec(num_bigint::BigInt::from(0b1101_u32), 4);
        let app = executor.ctx.terms.mk_app(extract, [input], Sort::bitvec(2));
        let value = executor.left_inverse_reeval(
            &Model::empty(),
            &HashMap::default(),
            &declared,
            &HashMap::default(),
            &mut HashMap::default(),
            app,
        );
        assert_eq!(
            value,
            Some(LiValue::BitVec {
                value: num_bigint::BigInt::from(3_u32),
                width: 2,
            })
        );
    }

    #[test]
    fn left_inverse_rejects_non_native_indexed_spellings_and_shadowing() {
        let executor = Executor::new();
        let indexed_user_bv_prefix = Symbol::indexed("bvtrap", vec![7]);
        let indexed_arithmetic = Symbol::indexed("+", vec![0]);
        let extract = Symbol::indexed("extract", vec![3, 2]);

        assert!(!Executor::left_inverse_application_is_native(
            &indexed_user_bv_prefix
        ));
        assert!(!Executor::left_inverse_application_is_native(
            &indexed_arithmetic
        ));
        assert!(!executor
            .li_symbol_is_delegable_interpreted(&indexed_user_bv_prefix, &HashSet::default(),));
        assert!(
            !executor.li_symbol_is_delegable_interpreted(&indexed_arithmetic, &HashSet::default(),)
        );

        let declared = HashSet::from_iter([extract.clone()]);
        assert!(Executor::left_inverse_application_is_native(&extract));
        assert!(
            !executor.li_symbol_is_delegable_interpreted(&extract, &declared),
            "an exact declared identity must not inherit interpreted BV semantics"
        );
    }

    #[test]
    fn non_exhaustive_int_samples_cannot_confirm_a_forall() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("x", Sort::Int);
        let body = executor.ctx.terms.mk_eq(x, x);
        let quant = executor
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        executor.ctx.assertions.push(quant);

        assert_eq!(
            executor.mbqi_soundness_gate_for_skipped_quantifiers(),
            SkippedQuantifierMbqiGate::Inconclusive,
            "checking a few integers is not a universal certificate"
        );
    }

    #[test]
    fn exhaustive_bool_domain_can_confirm_a_forall() {
        let mut executor = Executor::new();
        let b = executor.ctx.terms.mk_var("b", Sort::Bool);
        let not_b = executor.ctx.terms.mk_not(b);
        let body = executor.ctx.terms.mk_or(vec![b, not_b]);
        let quant = executor
            .ctx
            .terms
            .mk_forall(vec![("b".to_string(), Sort::Bool)], body);
        executor.ctx.assertions.push(quant);

        assert_eq!(
            executor.mbqi_soundness_gate_for_skipped_quantifiers(),
            SkippedQuantifierMbqiGate::ExhaustivelySatisfied,
            "both Boolean values exhaust the binder domain"
        );
    }

    #[test]
    fn nested_forall_is_not_misreported_as_no_quantifiers() {
        let mut executor = Executor::new();
        let b = executor.ctx.terms.mk_var("b", Sort::Bool);
        let not_b = executor.ctx.terms.mk_not(b);
        let body = executor.ctx.terms.mk_or(vec![b, not_b]);
        let quant = executor
            .ctx
            .terms
            .mk_forall(vec![("b".to_string(), Sort::Bool)], body);
        let p = executor.ctx.terms.mk_var("p", Sort::Bool);
        let wrapped = executor.ctx.terms.mk_or(vec![p, quant]);
        executor.ctx.assertions.push(wrapped);

        assert_eq!(
            executor.mbqi_soundness_gate_for_skipped_quantifiers(),
            SkippedQuantifierMbqiGate::Inconclusive,
            "a nested forall requires whole-formula validation"
        );
    }

    #[test]
    fn interpreted_bv_operator_classification_rejects_user_prefixes() {
        for builtin in [
            "bvadd",
            "bvsdiv",
            "bvredand",
            "concat",
            "extract",
            "int_to_bv",
        ] {
            assert!(
                is_interpreted_bv_symbol(builtin),
                "recognized BV operator {builtin} must stay interpreted"
            );
        }
        for user in ["bvtrap", "bvshadow", "bv", "bv_custom_solver_fn"] {
            assert!(
                !is_interpreted_bv_symbol(user),
                "user UF spelling {user} must not fabricate BV semantics"
            );
        }
    }
}

// =========================================================================
// DT-MBQI-Sat certificate gating (`AY_DT_CERT`) — module-level.
// =========================================================================

/// Budget: maximum distinct e-class keys (union across all table symbols) the
/// DT certificate will collect / check pointwise.
const MAX_DT_CERT_KEYS: usize = 64;
/// Budget: maximum default-vector combinations enumerated.
const MAX_DT_CERT_DEFAULT_COMBOS: usize = 16;
/// Budget: maximum default candidates per table symbol.
const MAX_DT_CERT_DEFAULTS_PER_SYM: usize = 6;
/// Depth bound on bounded constructor materialization (injectivity obligation).
const DT_CERT_FORM_DEPTH: u32 = 24;

/// `AY_DT_CERT` gating mode for [`Executor::try_dt_model_sat_certificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DtCertMode {
    /// Unset / `0` / `off`: the certificate never runs — byte-identical
    /// (the consult arms call it and it returns `None` before any clone/mint).
    Off,
    /// `shadow` / `log`: the certificate runs and logs its verdict, but NEVER
    /// flips the result (`Sat` is not granted).
    Shadow,
    /// `on` / `1` / `grant`: the certificate runs and GRANTS `Sat` on success.
    On,
}

/// Read the `AY_DT_CERT` gate fresh (the consult path is cold, so no cache is
/// needed and per-call reads keep test set/unset semantics reliable).
pub(crate) fn dt_cert_mode() -> DtCertMode {
    match std::env::var("AY_DT_CERT").ok().as_deref() {
        Some("on") | Some("1") | Some("grant") => DtCertMode::On,
        Some("shadow") | Some("log") => DtCertMode::Shadow,
        _ => DtCertMode::Off,
    }
}

/// `AY_DT_CERT_BRIDGE_ROUTE` gate for the W1 bridge-UF-over-constructor cert
/// route (SAT-side base-recheck campaign). Enabling it lets classification
/// audit bridge tautologies with the mandatory selector-bridge-premise gate,
/// but every grant remains withheld until selector-lambda interpretations can
/// be represented exactly in the published model. Unset/off remains
/// byte-identical everywhere (every read is lazily guarded).
pub(crate) fn dt_cert_bridge_route_enabled() -> bool {
    matches!(
        std::env::var("AY_DT_CERT_BRIDGE_ROUTE").ok().as_deref(),
        Some("1") | Some("on") | Some("shadow") | Some("log")
    )
}

/// Shadow-log a DT-certificate decision (reuse of the rejection-instrument
/// env-gated telemetry pattern). Silent when the gate is `Off`.
fn dt_cert_note(mode: DtCertMode, msg: &str) {
    if !matches!(mode, DtCertMode::Off) {
        eprintln!("c CERT/dt-mbqi-sat {msg}");
    }
}

// =========================================================================
// CONSTANT-INTERPRETATION SAT certificate gating (`AY_CONST_INTERP_CERT`)
// and budgets — module-level.
// =========================================================================

/// Immutable query/source/root scope shared by the affine quantified-certificate
/// publication packages below.
pub(in crate::executor) struct CertificateWitnessScope {
    query_epoch: crate::executor::QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
}

impl CertificateWitnessScope {
    fn for_current_query(executor: &Executor, roots: &[TermId]) -> Option<Self> {
        let root_entries: Vec<TermEntryStamp> = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect::<Option<_>>()?;
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: root_entries.into_boxed_slice(),
        })
    }

    fn is_current_for(&self, executor: &Executor, roots: &[TermId]) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == roots
            && self.root_entries.iter().copied().map(Some).eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
    }
}

/// Affine publication state for one checked finite/default-table model.
///
/// Both certificate variants install the exact model they proved into this
/// package. The package is usable only for the same public query, source scope,
/// and exact root vector; its fields and production constructor stay private
/// so the legacy Boolean marker cannot be paired with an arbitrary model. Any
/// ground projection is stamped and owned inside `model` itself.
pub(in crate::executor) enum FiniteTableWitnessState {
    /// Producer-owned model, before the public SAT funnel takes it.
    Pending {
        scope: CertificateWitnessScope,
        bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
        model: Box<Model>,
    },
    /// Exact pre-completed model is in transit to the publication slot but has
    /// not yet received its replacement-sensitive identity. No semantic write
    /// is permitted in this state.
    Staging {
        scope: CertificateWitnessScope,
        bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
    },
    /// Exact final model has been sealed after every semantic mutation.
    Installed {
        scope: CertificateWitnessScope,
        bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
        model_epoch: super::model::QuantifiedGrantModelEpoch,
    },
}

impl FiniteTableWitnessState {
    fn pending_for_current_query(
        executor: &mut Executor,
        roots: &[TermId],
        bindings: Vec<ay_frontend::CheckedProjectionBinding>,
        mut model: Model,
    ) -> Option<Self> {
        if !executor.complete_quantified_output_model_before_seal(&mut model, roots) {
            return None;
        }
        let scope = CertificateWitnessScope::for_current_query(executor, roots)?;
        if bindings.is_empty()
            || bindings
                .iter()
                .any(|binding| !executor.ctx.projection_binding_still_current(binding))
            || !model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            || !model.formula_neutral_function_defaults_are_current(&executor.ctx)
        {
            return None;
        }
        Some(Self::Pending {
            scope,
            bindings: bindings.into_boxed_slice(),
            model: Box::new(model),
        })
    }

    fn bindings_are_current(
        executor: &Executor,
        bindings: &[ay_frontend::CheckedProjectionBinding],
    ) -> bool {
        bindings
            .iter()
            .all(|binding| executor.ctx.projection_binding_still_current(binding))
    }

    pub(in crate::executor) fn is_pending_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
    ) -> bool {
        let Self::Pending {
            scope,
            bindings,
            model,
        } = self
        else {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/finite-table-current: state is not pending");
            }
            return false;
        };
        let epoch_current = scope
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch);
        let source_current = scope.source_context_stamp == executor.ctx.source_context_stamp();
        let roots_current = scope.roots.as_ref() == roots;
        let entries_current = scope.root_entries.iter().copied().map(Some).eq(roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root)));
        let bindings_current = Self::bindings_are_current(executor, bindings);
        let pins_current = model.quantified_certificate_pins_are_current(&executor.ctx.terms);
        let defaults_current = model.formula_neutral_function_defaults_are_current(&executor.ctx);
        let current = epoch_current
            && source_current
            && roots_current
            && entries_current
            && bindings_current
            && pins_current
            && defaults_current;
        if !current && ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/finite-table-current: epoch={epoch_current} source={source_current} roots={roots_current} entries={entries_current} bindings={bindings_current} pins={pins_current} defaults={defaults_current} certified_roots={:?} requested_roots={roots:?}",
                scope.roots
            );
        }
        current
    }

    pub(in crate::executor) fn into_staging(
        self,
        executor: &Executor,
        roots: &[TermId],
    ) -> Option<(Self, Model)> {
        let Self::Pending {
            scope,
            bindings,
            model,
        } = self
        else {
            return None;
        };
        if !scope.is_current_for(executor, roots)
            || !Self::bindings_are_current(executor, &bindings)
            || !model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            || !model.formula_neutral_function_defaults_are_current(&executor.ctx)
        {
            return None;
        }
        Some((Self::Staging { scope, bindings }, *model))
    }

    pub(in crate::executor) fn into_installed(
        self,
        executor: &Executor,
        roots: &[TermId],
        model: &Model,
        model_epoch: super::model::QuantifiedGrantModelEpoch,
    ) -> Option<Self> {
        let Self::Staging { scope, bindings } = self else {
            return None;
        };
        (scope.is_current_for(executor, roots)
            && Self::bindings_are_current(executor, &bindings)
            && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            && model.formula_neutral_function_defaults_are_current(&executor.ctx)
            && model.carries_quantified_grant_model(&model_epoch))
        .then_some(Self::Installed {
            scope,
            bindings,
            model_epoch,
        })
    }

    pub(in crate::executor) fn is_installed_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
        model: &Model,
    ) -> bool {
        matches!(self, Self::Installed { scope, bindings, model_epoch }
            if scope.is_current_for(executor, roots)
                && Self::bindings_are_current(executor, bindings)
                && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
                && model.formula_neutral_function_defaults_are_current(&executor.ctx)
                && model.carries_quantified_grant_model(model_epoch))
    }

    #[cfg(test)]
    pub(in crate::executor) fn for_test(
        executor: &Executor,
        roots: &[TermId],
        mut model: Model,
        pins: HashMap<TermId, EvalValue>,
    ) -> Option<Self> {
        model.install_quantified_certificate_pins(&executor.ctx.terms, pins)?;
        Some(Self::Pending {
            scope: CertificateWitnessScope::for_current_query(executor, roots)?,
            bindings: Box::new([]),
            model: Box::new(model),
        })
    }
}

/// Affine publication state for one checked constant interpretation.
///
/// The exact model owns the certified declaration/value entries. This state
/// transports only that affine model, its public query/source/root scope, and
/// finally the exact model epoch sealed at publication. Its fields are private
/// so a Boolean grant marker cannot be paired with an arbitrary model by
/// another executor component.
pub(in crate::executor) enum ConstInterpWitnessState {
    Pending {
        scope: CertificateWitnessScope,
        model: Box<Model>,
    },
    Staging {
        scope: CertificateWitnessScope,
    },
    Installed {
        scope: CertificateWitnessScope,
        model_epoch: super::model::QuantifiedGrantModelEpoch,
    },
}

impl ConstInterpWitnessState {
    fn pending_for_current_query(
        executor: &Executor,
        roots: &[TermId],
        model: Model,
    ) -> Option<Self> {
        let scope = CertificateWitnessScope::for_current_query(executor, roots)?;
        if !model.certified_const_interps_are_current(&executor.ctx)
            || !model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            || !model.formula_neutral_function_defaults_are_current(&executor.ctx)
        {
            return None;
        }
        Some(Self::Pending {
            scope,
            model: Box::new(model),
        })
    }

    pub(in crate::executor) fn is_pending_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
    ) -> bool {
        matches!(self, Self::Pending { scope, model }
            if scope.is_current_for(executor, roots)
                && model.certified_const_interps_are_current(&executor.ctx)
                && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
                && model.formula_neutral_function_defaults_are_current(&executor.ctx))
    }

    pub(in crate::executor) fn into_staging(
        self,
        executor: &Executor,
        roots: &[TermId],
    ) -> Option<(Self, Model)> {
        let Self::Pending { scope, model } = self else {
            return None;
        };
        if !scope.is_current_for(executor, roots)
            || !model.certified_const_interps_are_current(&executor.ctx)
            || !model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            || !model.formula_neutral_function_defaults_are_current(&executor.ctx)
        {
            return None;
        }
        Some((Self::Staging { scope }, *model))
    }

    pub(in crate::executor) fn into_installed(
        self,
        executor: &Executor,
        roots: &[TermId],
        model: &Model,
        model_epoch: super::model::QuantifiedGrantModelEpoch,
    ) -> Option<Self> {
        let Self::Staging { scope } = self else {
            return None;
        };
        (scope.is_current_for(executor, roots)
            && model.certified_const_interps_are_current(&executor.ctx)
            && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
            && model.formula_neutral_function_defaults_are_current(&executor.ctx)
            && model.carries_quantified_grant_model(&model_epoch))
        .then_some(Self::Installed { scope, model_epoch })
    }

    pub(in crate::executor) fn is_installed_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
        model: &Model,
    ) -> bool {
        matches!(self, Self::Installed { scope, model_epoch }
            if scope.is_current_for(executor, roots)
                && model.certified_const_interps_are_current(&executor.ctx)
                && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
                && model.formula_neutral_function_defaults_are_current(&executor.ctx)
                && model.carries_quantified_grant_model(model_epoch))
    }

    fn installed_entries_for_output<'a>(
        &self,
        executor: &Executor,
        model: &'a Model,
    ) -> Option<&'a [CertifiedConstInterpEntry]> {
        match self {
            Self::Installed { scope, model_epoch }
                if scope
                    .query_epoch
                    .is_same_epoch(&executor.query_authority_epoch)
                    && scope.source_context_stamp == executor.ctx.source_context_stamp()
                    && model.certified_const_interps_are_current(&executor.ctx)
                    && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
                    && model.formula_neutral_function_defaults_are_current(&executor.ctx)
                    && model.carries_quantified_grant_model(model_epoch) =>
            {
                Some(model.certified_const_interp_entries())
            }
            Self::Pending { .. } | Self::Staging { .. } => None,
            Self::Installed { .. } => None,
        }
    }
}

/// Budget: maximum snapshot assertions the certificate will consider.
const MAX_CONST_INTERP_ASSERTIONS: usize = 8;
/// Budget: maximum binders on any one `forall`.
const MAX_CONST_INTERP_BINDERS: usize = 6;
/// Budget: maximum uninterpreted heads actually PINNED by the interpretation.
/// Heads left free do not count (they cost nothing — the nested UNSAT already
/// quantifies over every interpretation of them).
const MAX_CONST_INTERP_HEADS: usize = 4;
/// Budget: maximum candidate interpretations enumerated.
const MAX_CONST_INTERP_COMBOS: usize = 32;
/// Budget: maximum isolated ground-solver calls across the whole certificate.
const MAX_CONST_INTERP_SOLVER_CALLS: usize = 24;
/// Budget: maximum term nodes visited by any one scan/substitution walk.
const MAX_CONST_INTERP_SCAN_WORK: u32 = 20_000;
/// Budget: wall clock for the WHOLE certificate, nested solves included.
///
/// This is an ACCEPTING step, so a fixed wall-clock budget makes the grant
/// machine-load sensitive (see the measured note on
/// `WHOLE_PROBLEM_RESOLVE_BUDGET_MS` in `unsat_cert.rs`). It is kept modest
/// deliberately: the certificate is grant-only, so expiry costs a grant we
/// might have had and never produces a wrong answer, and a longer budget
/// inside the quantifier lane would show up as bucket-count drift.
const CONST_INTERP_CERT_BUDGET_MS: u64 = 1_500;
/// Recursion bound on the sort walk that builds array candidates.
const CONST_INTERP_SORT_DEPTH: u32 = 4;
/// Budget: extra candidate constants added per head by the widened pass.
///
/// Two is what the measured shapes need — a head is pinned by at most a couple
/// of authored equalities, and the model contributes one. Keeping it small is
/// what keeps the widened combination space inside
/// [`MAX_CONST_INTERP_COMBOS`] / [`MAX_CONST_INTERP_SOLVER_CALLS`]; a head
/// with more pins than this simply gets the first two, and the pass declines
/// exactly as it does today.
const MAX_CONST_INTERP_EXTRA_CANDIDATES: usize = 2;

/// Which constants a pinned head is enumerated over.
///
/// The certificate runs the `FixedFamily` pass FIRST and unchanged, so nothing
/// that grants today can be lost; `WithProblemConstants` runs only after that
/// declined. See the two-pass note on
/// [`Executor::try_const_interp_sat_certificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstInterpCandidateSource {
    /// The fixed closed-constant family of the head's result sort
    /// ([`Executor::const_interp_candidates`]) — `false/true`, `0/1`, the
    /// const-`0` array. Byte-identical to the pre-widening certificate.
    FixedFamily,
    /// The fixed family PLUS constants the problem itself names for the head
    /// ([`Executor::const_interp_widened_candidates`]).
    WithProblemConstants,
}

/// Node-visit cap for the closed-valid-sentence PARTITION walk. Exceeding it
/// declines (fail-closed): the walk is scope-carrying and unmemoised, so a
/// pathological DAG must not be allowed to spin.
const VALID_SENTENCE_PARTITION_NODE_CAP: u32 = 200_000;

thread_local! {
    /// Re-entrancy depth for the constant-interpretation certificate.
    ///
    /// The certificate's accepting step runs nested solves, and those solves
    /// can reach the quantifier lane's certificate consult sites. Admitting
    /// the certificate only at depth 0 bounds the recursion; a nested solve
    /// simply declines and answers with plain solving, which terminates. Same
    /// shape as `TRUST_DISCHARGE_DEPTH` in `unsat_cert.rs`, and for the same
    /// reason: a `&mut self` flag does not survive a fresh `Executor`.
    static CONST_INTERP_CERT_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// `AY_CONST_INTERP_CERT` gating mode for
/// [`Executor::try_const_interp_sat_certificate`].
///
/// DEFAULTS TO [`ConstInterpCertMode::On`], unlike [`DtCertMode`]. The staging
/// ladder exists for model GUESSERS, whose grant rests on a sampled candidate
/// model; this certificate's accepting step is an `Unsat` from AY's own
/// mandatory-certified funnel, which is strictly stronger evidence. `Shadow`
/// stays available for debugging (run + log + withhold the verdict) and `Off`
/// for a byte-identical bisect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstInterpCertMode {
    /// `off` / `0`: never runs — byte-identical (no scan, no mint, no log).
    Off,
    /// Runs and logs its verdict, but NEVER grants `Sat`. (B17: currently
    /// unconstructed — the env spelling that selected it is retired; a CLI
    /// mode can reinstate it if a measurement needs it.)
    #[allow(dead_code)]
    Shadow,
    /// Anything else, INCLUDING UNSET: runs and GRANTS `Sat` on success.
    On,
}

/// The constant-interpretation certificate gate. B17: the CLI-populated
/// global (--no-const-interp-cert) replaced the never-set env var; the
/// diagnostic shadow mode retired with it, unmeasured — reinstate it as a
/// CLI mode if a measurement ever needs it.
pub(crate) fn const_interp_cert_mode() -> ConstInterpCertMode {
    if ay_core::theory_disable_flags().no_const_interp_cert {
        ConstInterpCertMode::Off
    } else {
        ConstInterpCertMode::On
    }
}

/// True when [`ay_core::TermStore::rebuild_app`] has a FOLDING arm for `name`,
/// i.e. when rebuilding an application of this spelling would route it through
/// a builtin constructor rather than re-interning it as an opaque `App`.
///
/// Used only to fail closed: a user symbol wearing one of these spellings must
/// never sit above a node the certificate rewrites. Deliberately a SUPERSET of
/// the real dispatch table — an extra name here costs a decline, a missing one
/// would cost soundness.
fn const_interp_rebuild_folds_name(name: &str) -> bool {
    is_pure_arith_bool_symbol(name)
        || is_finite_table_interpreted_symbol(name)
        || is_interpreted_bv_symbol(name)
        || name.starts_with("bv")
        || matches!(
            name,
            "implies"
                | "rem"
                | "select"
                | "store"
                | "concat"
                | "extract"
                | "repeat"
                | "rotate_left"
                | "rotate_right"
                | "zero_extend"
                | "sign_extend"
                | "const-array"
        )
}

/// Log a constant-interpretation certificate decision.
///
/// The gate defaults to `On`, so — unlike `dt_cert_note` — this must NOT print
/// merely because the certificate is enabled. It speaks only in `Shadow` mode
/// or under the existing `--debug-cert` trace channel.
fn const_interp_note(mode: ConstInterpCertMode, msg: &str) {
    if matches!(mode, ConstInterpCertMode::Shadow) || ay_core::misc_cli_flags().debug_cert {
        eprintln!("c CERT/const-interp {msg}");
    }
}

#[cfg(test)]
mod bridge_route_tests;

#[cfg(test)]
mod valid_closed_sentence_cert_tests {
    use super::*;
    use ay_frontend::parse;

    /// Build an executor with the script's declarations and assertions in
    /// place, WITHOUT a `check-sat` — the certificate is exercised directly.
    ///
    /// NOTE for anyone extending these: pick sentences that SURVIVE
    /// simplification. A tautology like `∀x. f(x) = f(x)` is folded to `true`
    /// before it reaches `ctx.assertions`, so it no longer mentions `f` and
    /// tests nothing about the partition.
    fn executor_for(input: &str) -> Executor {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        exec.execute_all(&commands).unwrap();
        exec
    }

    /// The declared-symbol set the certificate builds internally.
    fn declared_of(exec: &Executor) -> HashSet<String> {
        exec.ctx
            .symbol_iter()
            .map(|(name, info)| exec.ctx.symbol_identity_name(name, info).to_string())
            .collect()
    }

    /// REJECTING DIRECTION — the guard that keeps this certificate from
    /// becoming a rubber stamp.
    ///
    /// "Nothing to pin" must mean the sentence genuinely contains no
    /// uninterpreted symbol. If it were allowed to mean "the emitted witness
    /// happened to pin nothing", the certificate would swallow the
    /// auflia-model escape class (∀∃ over a printed `f`), where substitution
    /// consumes every model symbol and leaves nothing to pin.
    #[test]
    fn declines_sentence_naming_an_uninterpreted_function() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int)) (> (f x) 0)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(
            !exec.closed_sentence_without_uninterpreted_symbols(assertions[0], &declared_of(&exec)),
            "a sentence mentioning the uninterpreted head `f` is outside the partition"
        );
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "the certificate must decline a sentence with an uninterpreted head"
        );
    }

    /// Same rejecting direction for an uninterpreted CONSTANT (arity 0).
    /// Excluding arity-0 symbols is what keeps "nothing to interpret"
    /// literally true; admitting them would hand the certificate sentences
    /// whose truth really does depend on an interpretation.
    #[test]
    fn declines_sentence_naming_an_uninterpreted_constant() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (declare-const c Int)
             (assert (forall ((x Int)) (>= x c)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(
            !exec.closed_sentence_without_uninterpreted_symbols(assertions[0], &declared_of(&exec)),
            "a sentence mentioning the uninterpreted constant `c` is outside the partition"
        );
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "the certificate must decline a sentence with an uninterpreted constant"
        );
    }

    /// REJECTING DIRECTION, and the sharpest form of it: the sentence is VALID
    /// — so the accepting step could well refute its negation — and it is
    /// still declined, purely because it names `f`. Validity is NOT the
    /// admission criterion; "no uninterpreted symbol to interpret" is.
    #[test]
    fn declines_a_valid_sentence_that_still_names_an_uninterpreted_head() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int)) (or (> (f x) 0) (<= (f x) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        // Guard the test itself: if simplification ever folds this to `true`
        // the sentence stops mentioning `f` and the test would silently stop
        // testing the partition.
        if exec.closed_sentence_without_uninterpreted_symbols(assertions[0], &declared_of(&exec)) {
            return;
        }
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "a VALID sentence naming an uninterpreted head must still be declined"
        );
    }

    /// REJECTING DIRECTION — the soundness canary. `∀x:Int. x > 0` is closed
    /// and symbol-free, so it PASSES the outer partition; it is also FALSE and
    /// does not match the exact parity theorem.
    #[test]
    fn declines_a_false_closed_sentence() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (> x 0)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(
            exec.closed_sentence_without_uninterpreted_symbols(assertions[0], &declared_of(&exec)),
            "the sentence is closed and symbol-free — it is the exact theorem step, \
             not the partition, that must reject it"
        );
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "certifying a FALSE sentence would be a wrong `sat`"
        );
    }

    /// ACCEPTING DIRECTION: `∀x:Int. (2|x ∨ 2|x+1)` is closed, names no
    /// uninterpreted symbol, and is valid.
    #[test]
    fn grants_a_valid_symbol_free_closed_sentence() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod (+ x 1) 2) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(
            exec.closed_sentence_without_uninterpreted_symbols(assertions[0], &declared_of(&exec))
        );
        assert!(exec.is_exact_closed_parity_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_some(),
            "the structurally rechecked parity theorem must retain its grant"
        );
    }

    #[test]
    fn grants_exact_unbounded_above_forall_exists_sentence() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(exec.is_exact_closed_unbounded_above_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_some(),
            "`y := x+1` is an exact witness for the admitted theorem"
        );
    }

    #[test]
    fn grants_exact_literal_floor_forall_exists_sentence() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int))
                (exists ((y Int)) (and (> y x) (> y 5)))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(exec.is_exact_closed_unbounded_above_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_some(),
            "`y := max(x,5)+1` is an exact witness for both strict lower bounds"
        );
    }

    /// FALSE near-shape mutant: replacing the literal lower bound `5 < y`
    /// with the upper bound `y < 5` makes the sentence false for `x >= 5`.
    #[test]
    fn declines_bounded_above_forall_exists_mutant() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int))
                (exists ((y Int)) (and (> y x) (< y 5)))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.is_exact_closed_unbounded_above_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "an upper-bounded existential must never inherit unbounded-above authority"
        );
    }

    /// A same-spelled inner binder changes every occurrence's binding identity
    /// and makes the visible `<` reflexive; reject rather than name-match.
    #[test]
    fn declines_shadowed_forall_exists_binder_mutant() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((x Int)) (< x x))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.is_exact_closed_unbounded_above_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "same-name binder shadowing is outside the exact theorem"
        );
    }

    #[test]
    fn exact_closed_sentence_evidence_installs_only_its_ordered_roots() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod (+ x 1) 2) 0))))
             (assert (forall ((n Int)) (exists ((m Int)) (> m n))))",
        );
        let roots = exec.ctx.assertions.clone();
        let evidence = exec
            .try_valid_closed_sentence_sat_certificate(&roots, LogicCategory::Lia)
            .expect("both exact structural theorems are checked");
        assert!(exec.install_exact_closed_sentence_sat_authority(evidence));
        let grant = exec
            .mbqi_sat_cert_query_grant
            .as_ref()
            .expect("consumption installs a typed grant");
        assert!(grant.is_current_for(&exec, &roots));

        let mut reordered = roots.clone();
        reordered.reverse();
        assert_ne!(reordered, roots);
        assert!(
            !grant.is_current_for(&exec, &reordered),
            "the consumed evidence cannot be retargeted to reordered roots"
        );
    }

    #[test]
    fn model_free_exact_closed_sentence_authority_survives_sat_emission() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
        );
        let roots = exec.ctx.assertions.clone();
        let evidence = exec
            .try_valid_closed_sentence_sat_certificate(&roots, LogicCategory::Lia)
            .expect("exact structural theorem is checked");
        assert!(exec.install_exact_closed_sentence_sat_authority(evidence));
        assert!(exec.has_current_model_free_mbqi_sat_authority(&roots));
        assert!(
            exec.last_model.is_none(),
            "the theorem producer must not rely on a hidden model fixture"
        );
        exec.last_model_validated = false;
        exec.last_result = Some(SolveResult::Sat);

        let emitted = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("model-free theorem emission is fail-closed, not fallible");

        assert_eq!(emitted, SolveResult::Sat);
        assert!(exec.mbqi_sat_cert_grant_active);
        assert!(exec
            .mbqi_sat_cert_query_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(&exec, &roots)));
        assert!(
            exec.last_model.is_some(),
            "SAT emission must construct a canonical observable witness"
        );
        assert!(exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_some());
    }

    #[test]
    fn exact_closed_sentence_install_retires_competing_routing_state() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
        );
        let roots = exec.ctx.assertions.clone();
        let evidence = exec
            .try_valid_closed_sentence_sat_certificate(&roots, LogicCategory::Lia)
            .expect("exact structural theorem is checked");

        exec.finite_table_cert_witness_state = Some(
            FiniteTableWitnessState::for_test(&exec, &roots, Model::empty(), Default::default())
                .expect("current stale-route fixture"),
        );
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.dt_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;

        assert!(exec.install_exact_closed_sentence_sat_authority(evidence));

        assert!(!exec.finite_table_cert_grant_active);
        assert!(exec.finite_table_cert_witness_state.is_none());
        assert!(!exec.const_interp_cert_grant_active);
        assert!(exec.const_interp_cert_witness_state.is_none());
        assert!(!exec.dt_cert_grant_active);
        assert!(exec.dt_cert_query_grant.is_none());
        assert!(!exec.bv_quantifier_full_domain_proof);
        assert!(exec.bv_quantifier_full_domain_query_grant.is_none());
        assert!(exec.mbqi_sat_cert_grant_active);
        assert!(exec.has_current_model_free_mbqi_sat_authority(&roots));
    }

    #[test]
    fn exact_closed_sentence_evidence_rejects_stale_epoch_and_source() {
        let mut stale_epoch = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
        );
        let epoch_roots = stale_epoch.ctx.assertions.clone();
        let epoch_evidence = stale_epoch
            .try_valid_closed_sentence_sat_certificate(&epoch_roots, LogicCategory::Lia)
            .expect("exact theorem is checked");
        stale_epoch.advance_query_authority_epoch();
        assert!(!stale_epoch.install_exact_closed_sentence_sat_authority(epoch_evidence));
        assert!(!stale_epoch.mbqi_sat_cert_grant_active);

        let mut stale_source = executor_for(
            "(set-logic LIA)
             (assert (forall ((x Int)) (exists ((y Int)) (> y x))))",
        );
        let source_roots = stale_source.ctx.assertions.clone();
        let source_evidence = stale_source
            .try_valid_closed_sentence_sat_certificate(&source_roots, LogicCategory::Lia)
            .expect("exact theorem is checked");
        let source_epoch = stale_source.query_authority_epoch.clone();
        assert!(stale_source
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds")
            .is_none());
        // Restore only the epoch to isolate the source/scope binding.
        stale_source.query_authority_epoch = source_epoch;
        assert!(!stale_source.install_exact_closed_sentence_sat_authority(source_evidence));
        assert!(!stale_source.mbqi_sat_cert_grant_active);
    }

    /// FALSE near-shape mutant: changing modulus 2 to 3 leaves `x = 1`
    /// uncovered. A sampled QE/solver result must never promote this shape.
    #[test]
    fn declines_parity_modulus_mutant() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (assert (forall ((x Int)) (or (= (mod x 3) 0) (= (mod (+ x 1) 3) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.is_exact_closed_parity_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "a different modulus is outside the exact theorem"
        );
    }

    /// FALSE near-shape mutant: `x` and `x+2` have the same parity, so odd
    /// `x` falsifies both disjuncts.
    #[test]
    fn declines_parity_offset_mutant() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod (+ x 2) 2) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.is_exact_closed_parity_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "a different successor offset is outside the exact theorem"
        );
    }

    /// Even another VALID symbol-free sentence must decline unless its theorem
    /// is represented by this independently checked structural kernel. This
    /// pins the removal of generic solver/deep-QE authority.
    #[test]
    fn declines_unrecognized_valid_closed_sentence() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (assert (forall ((x Int)) (or (= (mod x 2) 0) (= (mod (+ x -1) 2) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(contains_quantifier(&exec.ctx.terms, assertions[0]));
        assert!(!exec.is_exact_closed_parity_theorem(assertions[0]));
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "validity discovered by a solver or sampled QE is not grant authority"
        );
    }

    /// A user declaration wearing a load-bearing operator spelling must not be
    /// confused with the canonical interpreted operator, even when its body is
    /// textually identical to the parity theorem.
    #[test]
    fn declines_source_shadowed_parity_operator() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (declare-fun |or| (Bool Bool) Bool)
             (assert (forall ((x Int))
                (|or| (= (mod x 2) 0) (= (mod (+ x 1) 2) 0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.exact_closed_sentence_operators_are_unshadowed());
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "a source-shadowed `or` must not inherit the builtin theorem"
        );
    }

    /// The unbounded-above theorem has the same declaration-identity
    /// perimeter: a user symbol spelled `<` is not integer ordering.
    #[test]
    fn declines_source_shadowed_unbounded_above_operator() {
        let mut exec = executor_for(
            "(set-logic ALL)
             (declare-fun |<| (Int Int) Bool)
             (assert (forall ((x Int)) (exists ((y Int)) (|<| x y))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_eq!(assertions.len(), 1);
        assert!(!exec.exact_closed_sentence_operators_are_unshadowed());
        assert!(
            exec.try_valid_closed_sentence_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "a source-shadowed `<` must not inherit integer-order authority"
        );
    }
}

/// Partition tests for the constant-interpretation certificate's GROUND
/// CONJUNCT admission (step 1 of [`Executor::const_interp_cert_inner`]).
///
/// The certificate used to require every snapshot assertion to be a top-level
/// `forall`, on the correct grounds that certifying only the `forall`s of a
/// mixed snapshot would prove SAT of a strict SUBSET of it — a wrong-SAT. The
/// widening admits ground conjuncts and DISCHARGES them under the same shared
/// interpretation `I`, so the certified statement keeps its full strength.
///
/// These are the REJECTING-DIRECTION tests for that widening: each is a
/// snapshot the widened partition must still refuse, or a mixed snapshot whose
/// ground conjunct `I` cannot satisfy. A grant in any of them would be exactly
/// the wrong-SAT the original all-`forall` partition was protecting against.
#[cfg(test)]
mod const_interp_ground_conjunct_tests {
    use super::*;
    use ay_frontend::parse;

    fn executor_for(input: &str) -> Executor {
        let commands = parse(input).unwrap();
        let mut exec = Executor::new();
        exec.execute_all(&commands).unwrap();
        exec
    }

    /// REJECTING DIRECTION — the core of the widening. The `forall` is
    /// satisfied by the constant interpretation `a := const-array 0`, but the
    /// ground conjunct `(= (select a 5) 1)` is FALSE under that same `I`.
    /// Certifying the `forall` alone would be the subset wrong-SAT; the ground
    /// discharge must reject the combination and the certificate must decline.
    #[test]
    fn declines_when_a_ground_conjunct_is_false_under_the_interpretation() {
        let mut exec = executor_for(
            "(set-logic AUFLIA)
             (declare-fun a () (Array Int Int))
             (assert (forall ((x Int)) (= (select a x) 0)))
             (assert (= (select a 5) 1))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Auflia)
                .is_none(),
            "a ground conjunct falsified by `I` must sink the whole certificate, \
             not be silently skipped while the forall is certified"
        );
    }

    /// REJECTING DIRECTION — the ground conjunct is UNSATISFIABLE on its own
    /// (`0 = 1`), so no interpretation of anything can rescue it. The `forall`
    /// is trivially satisfiable, so this isolates the ground obligation.
    #[test]
    fn declines_when_a_ground_conjunct_is_unsatisfiable() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (declare-const c Int)
             (assert (forall ((x Int)) (= (f x) (f x))))
             (assert (and (= c 0) (= c 1)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Uflia)
                .is_none(),
            "an unsatisfiable ground conjunct must never be certified"
        );
    }

    /// REJECTING DIRECTION — the admission test stays SYNTACTIC and
    /// fail-closed. A non-`forall` assertion carrying an `exists` is outside
    /// the class (the certificate discharges a `forall` by refuting its
    /// negation at fresh constants; it has no such story for an existential),
    /// so it must decline rather than treat the assertion as ground.
    #[test]
    fn declines_a_ground_assertion_containing_an_exists() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int)) (>= (f x) 0)))
             (assert (exists ((y Int)) (= (f y) 7)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Uflia)
                .is_none(),
            "an `exists` conjunct is out of class and must decline, not be \
             admitted as a ground conjunct"
        );
    }

    /// REJECTING DIRECTION — an all-ground snapshot has no `forall` and is the
    /// ordinary pipeline's job end-to-end. Requiring at least one `forall`
    /// keeps the widening from taking over a decision made elsewhere.
    #[test]
    fn declines_an_all_ground_snapshot() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-const c Int)
             (assert (>= c 0))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Uflia)
                .is_none(),
            "a snapshot with no forall is out of this certificate's class"
        );
    }

    /// EVIDENCE (not a behavioural pin for the public verdict): the
    /// `closed_universal_validity_precheck::open_universal_with_free_const_stays_sat`
    /// shape — a `forall` whose body mentions a FREE DECLARED CONSTANT, plus a
    /// ground conjunct about that same constant — IS inside the widened
    /// certificate's accepting class (`I` picks `x := 0`, satisfying both
    /// `forall q0. q0 + x >= q0` and `x >= 0`).
    ///
    /// That query nevertheless still answers `unknown` end-to-end, because on
    /// its route the verdict is degraded in `executor/model/validation` before
    /// any certificate consult site is reached (measured: `:unknown.phase
    /// "model-validation"`, and `--debug-cert` shows no const-interp line at
    /// all). This test pins WHERE the remaining gap is: the certificate is
    /// ready, the consult arm is missing.
    #[test]
    fn accepts_the_free_constant_shape_that_the_public_route_never_consults_it_for() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (declare-fun x () Int)
             (assert (forall ((q0 Int)) (>= (+ q0 x) q0)))
             (assert (>= x 0))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Lia)
                .is_some(),
            "forall-with-free-constant plus a ground conjunct is inside the \
             widened accepting class; if this ever fails the widening regressed"
        );
    }

    #[test]
    fn replaces_a_foreign_model_and_reinstalls_the_exact_checked_interpretation() {
        let mut exec = executor_for(
            "(set-option :produce-models true)
             (set-logic UFLIA)
             (declare-fun p (Int) Bool)
             (assert (forall ((x Int)) (p x)))",
        );
        let assertions = exec.ctx.assertions.clone();
        let sentinel = exec.ctx.terms.mk_bool(false);
        let mut foreign_model = Model::empty();
        foreign_model
            .completed_values
            .insert(sentinel, EvalValue::Bool(true));
        exec.last_model = Some(foreign_model);

        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Uflia)
                .is_some(),
            "the constant interpretation p := true certifies this universal"
        );
        assert!(
            exec.last_model
                .as_ref()
                .expect("the producer leaves the predecessor installed until publication")
                .completed_values
                .contains_key(&sentinel),
            "the affine witness remains parked until the public funnel"
        );
        assert!(
            exec.const_interp_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_pending_current_for(&exec, &assertions)),
            "the parked witness must be scoped to the checked public roots"
        );
        let extra_root = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(extra_root);
        assert!(
            !exec
                .const_interp_cert_witness_state
                .as_ref()
                .expect("parked checked interpretation")
                .is_pending_current_for(&exec, &exec.ctx.assertions),
            "a different root window must not reuse the witness"
        );
        exec.ctx.assertions.pop();

        // Reproduce the mapper hazard: a later nested probe replaces the live
        // model while leaving the affine parked witness intact.
        let mut overwritten_model = Model::empty();
        overwritten_model
            .completed_values
            .insert(sentinel, EvalValue::Bool(true));
        exec.last_model = Some(overwritten_model);
        exec.const_interp_cert_grant_active = true;
        exec.last_model_validated = true;

        let emitted = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("SAT emission must remain fail-closed, not error");
        assert_eq!(emitted, SolveResult::Sat);
        assert!(exec
            .const_interp_cert_witness_state
            .as_ref()
            .is_some_and(|state| state.is_installed_current_for(
                &exec,
                &assertions,
                exec.last_model.as_ref().expect("published model")
            )));
        let three = exec.ctx.terms.mk_int(num_bigint::BigInt::from(3));
        let p_three = exec
            .ctx
            .terms
            .mk_app(Symbol::named("p"), [three], Sort::Bool);
        let model = exec
            .last_model
            .as_ref()
            .expect("published SAT carries the checked interpretation");
        assert_eq!(exec.evaluate_term(model, p_three), EvalValue::Bool(true));
        let model_text = exec.model();
        assert!(
            model_text.contains("(define-fun p ((x!0 Int)) Bool\n    true)"),
            "get-model must print the exact certified interpretation: {model_text}"
        );
        assert_eq!(
            exec.values(&[("(p 3)".to_string(), p_three)]),
            "(((p 3) true))",
            "get-value and get-model must read the same model-owned package"
        );
        assert!(
            !model.completed_values.contains_key(&sentinel),
            "the public funnel must reinstall the parked model, not publish the probe model"
        );
    }

    // =====================================================================
    // CANDIDATE WIDENING (`ConstInterpCandidateSource::WithProblemConstants`)
    //
    // Pass 1 enumerates the fixed `false/true`, `0/1`, const-`0` family. Pass 2
    // adds constants the PROBLEM names for a head. These tests pin both that
    // the widening buys the intended grants and that it buys nothing else: a
    // candidate is a GUESS, and the accepting step (substitute, refute the
    // negation with an independent solver `Unsat`) is unchanged and is the only
    // thing that can turn a guess into a grant.
    // =====================================================================

    /// Run one pass in isolation, so a test can prove a grant came from the
    /// WIDENING rather than from the fixed family it already had.
    fn cert_pass(
        exec: &mut Executor,
        assertions: &[TermId],
        category: LogicCategory,
        source: ConstInterpCandidateSource,
    ) -> Option<()> {
        let mode = const_interp_cert_mode();
        let deadline = ay_core::time::Instant::now()
            + std::time::Duration::from_millis(CONST_INTERP_CERT_BUDGET_MS);
        exec.const_interp_cert_inner(assertions, category, mode, deadline, source)
    }

    /// Fail loudly if a fixture folded away before the certificate saw it —
    /// the previous round of rejecting tests passed vacuously because their
    /// examples simplified to `true` at parse time.
    fn assert_fixture_is_live(exec: &Executor, assertions: &[TermId], expected_len: usize) {
        assert_eq!(
            assertions.len(),
            expected_len,
            "fixture lost an assertion before the certificate saw it"
        );
        for &a in assertions {
            assert!(
                !matches!(exec.ctx.terms.get(a), TermData::Const(_)),
                "fixture folded to a constant before the certificate saw it — \
                 it would be testing nothing"
            );
        }
    }

    /// REJECTING DIRECTION — the widening's own canary. `(= a 5)` names `5`,
    /// so pass 2 really does try `I(a) := 5`; under that `I` the universal
    /// `∀x:Int. a > x` is FALSE (take `x = 5`). Only the accepting step stands
    /// between the new candidate and a wrong `sat`, and it must refuse.
    ///
    /// Both passes are exercised explicitly so the test cannot pass merely
    /// because pass 2 never ran.
    #[test]
    fn widening_declines_a_named_constant_that_falsifies_the_forall() {
        let mut exec = executor_for(
            "(set-logic LIA)
             (declare-const a Int)
             (assert (= a 5))
             (assert (forall ((x Int)) (> a x)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_fixture_is_live(&exec, &assertions, 2);
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Lia,
                ConstInterpCandidateSource::WithProblemConstants,
            )
            .is_none(),
            "`a := 5` satisfies the ground pin but falsifies `∀x. a > x`; \
             certifying it would be a wrong `sat`"
        );
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Lia)
                .is_none(),
            "neither pass may certify an unsatisfiable snapshot"
        );
    }

    /// REJECTING DIRECTION — a FUNCTION head whose authored pins are mutually
    /// inconsistent with a constant interpretation. `f(0) = -2` and `f(5) = 3`
    /// name both `-2` and `3`, so pass 2 tries `λy. -2` and `λy. 3`; each
    /// falsifies the other ground conjunct. The strict-monotonicity universal
    /// additionally rules out every constant function. Must decline.
    #[test]
    fn widening_declines_when_no_single_named_constant_satisfies_all_pins() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int) (y Int))
               (=> (and (<= 0 x) (< x y) (<= y 5)) (< (f x) (f y)))))
             (assert (= (f 0) (- 2)))
             (assert (= (f 5) 3))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_fixture_is_live(&exec, &assertions, 3);
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Uflia,
                ConstInterpCandidateSource::WithProblemConstants,
            )
            .is_none(),
            "two disagreeing pins admit no constant function — the widened \
             candidates must each be refuted, not accepted"
        );
    }

    /// REJECTING DIRECTION — pass 2 must not resurrect a snapshot the
    /// PARTITION rejects. The named constant `7` would satisfy the universal,
    /// but the sibling assertion carries an `exists`, which is out of class.
    /// The partition runs before candidates are built, so the widening cannot
    /// reach it.
    #[test]
    fn widening_does_not_bypass_the_partition() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int)) (= (f x) 7)))
             (assert (exists ((y Int)) (= (f y) 7)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_fixture_is_live(&exec, &assertions, 2);
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Uflia,
                ConstInterpCandidateSource::WithProblemConstants,
            )
            .is_none(),
            "the syntactic partition is unchanged by the widening"
        );
    }

    /// ACCEPTING DIRECTION — the shape the widening exists for, and proof that
    /// it is the widening doing the work: pass 1 (fixed `0/1` family) CANNOT
    /// satisfy `a = 3/2`, pass 2 reads `3/2` off the problem and certifies.
    #[test]
    fn widening_certifies_a_snapshot_whose_witness_value_the_problem_names() {
        let mut exec = executor_for(
            "(set-logic LRA)
             (declare-fun a () Real)
             (assert (= a 1.5))
             (assert (forall ((x Real))
               (=> (and (>= x 0.0) (<= x a)) (<= x 2.0))))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_fixture_is_live(&exec, &assertions, 2);
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Lra,
                ConstInterpCandidateSource::FixedFamily,
            )
            .is_none(),
            "the fixed 0/1 family cannot satisfy `a = 3/2` — if this ever \
             grants, the accepting-direction test below proves nothing"
        );
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Lra,
                ConstInterpCandidateSource::WithProblemConstants,
            )
            .is_some(),
            "`I(a) := 3/2` satisfies the ground pin AND the guarded universal"
        );
    }

    /// ACCEPTING DIRECTION — a FUNCTION head. `f(0) = f(5) = -2` names `-2`,
    /// and `λy. -2` satisfies the ground pins and the NON-strict monotonicity
    /// universal (`-2 <= -2`). Twin of the strict-gap rejecting test above:
    /// same shape, different comparison, opposite verdict.
    #[test]
    fn widening_certifies_a_constant_function_the_problem_names() {
        let mut exec = executor_for(
            "(set-logic UFLIA)
             (declare-fun f (Int) Int)
             (assert (forall ((x Int) (y Int))
               (=> (and (<= 0 x) (< x y) (<= y 5)) (<= (f x) (f y)))))
             (assert (= (f 0) (- 2)))
             (assert (= (f 5) (- 2)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert_fixture_is_live(&exec, &assertions, 3);
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Uflia,
                ConstInterpCandidateSource::FixedFamily,
            )
            .is_none(),
            "neither `0` nor `1` satisfies `f(0) = -2`"
        );
        assert!(
            cert_pass(
                &mut exec,
                &assertions,
                LogicCategory::Uflia,
                ConstInterpCandidateSource::WithProblemConstants,
            )
            .is_some(),
            "`λy. -2` satisfies every conjunct — the widening's accepting class"
        );
    }

    /// ACCEPTING DIRECTION — the shape the widening exists for. `I` sets
    /// `a := const-array 0`, which satisfies BOTH the pointwise `forall` and
    /// the ground const-array equality. Pins the grant so a future narrowing
    /// cannot silently drop it.
    #[test]
    fn certifies_a_mixed_snapshot_when_one_interpretation_satisfies_all_of_it() {
        let mut exec = executor_for(
            "(set-logic AUFLIA)
             (declare-fun a () (Array Int Int))
             (assert (= a ((as const (Array Int Int)) 0)))
             (assert (forall ((x Int)) (= (select a x) 0)))",
        );
        let assertions = exec.ctx.assertions.clone();
        assert!(
            exec.try_const_interp_sat_certificate(&assertions, LogicCategory::Auflia)
                .is_some(),
            "one constant interpretation satisfies every conjunct — this is the \
             widening's accepting class"
        );
    }
}
