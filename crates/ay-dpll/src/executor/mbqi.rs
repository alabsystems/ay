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
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

use super::model::EvalValue;
use super::model::Model;
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
    BoxHead,
    /// `Unbox` of a left-inverse axiom. Materialized as the inverse of its
    /// partner `Box` on the `BoxPoint` family, and as the designated
    /// per-sort fallback value everywhere else (see `left_inverse_fallback`).
    UnboxHead {
        /// The partner `Box` symbol whose `BoxPoint`s this head inverts.
        box_sym: String,
        /// The axiom's binder sort `S` = this head's result sort (fixed by
        /// well-sortedness of `Unbox(Box x) = x`), used to pick the fallback.
        result_sort: Sort,
    },
    /// Head `f` of a unary identity definition `forall x:T. f(x) = x`.
    /// Materialized as the identity function on `T` (over ANY universe).
    IdentityHead,
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
    BoxPoint(String, Box<LiValue>),
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
type LiUfKey = (String, Vec<LiValue>);

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
    ) -> Option<Result<SolveResult>> {
        if unhandled_quantifiers.is_empty() {
            return None;
        }

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
            if let Some(result) = self.try_bv_mbqi_refinement(&bv_quants, category) {
                match result {
                    Ok(SolveResult::Unsat(_)) => return Some(result),
                    Ok(SolveResult::Sat) if other_quants.is_empty() => return Some(result),
                    // BV-MBQI returned SAT but there are non-BV quantifiers remaining —
                    // fall through to generic MBQI for those.
                    Ok(SolveResult::Sat) => {}
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
        let forall_quants: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();

        if forall_quants.is_empty() {
            return SkippedQuantifierMbqiGate::NoQuantifiers;
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
        vars: &[(String, Sort)],
        body: TermId,
    ) -> UfCompletionEval {
        if self.assertions_force_false(ground_instance) {
            return UfCompletionEval::False;
        }
        if self.term_supported_by_uf_completion(ground_instance)
            || self.quantifier_is_constant_uf_definition(vars, body)
            || self.quantifier_is_uf_definition(vars, body)
            || self.quantifier_is_total_true_bool_predicate(vars, body)
            || self.ground_body_is_propositional_tautology(ground_instance)
        {
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
        if std::env::var_os("AY_DEBUG_CERT").is_some() {
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
    fn term_mentions_completable_uf(&self, term: TermId) -> bool {
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
        // NOTE: deliberately does NOT thread the quantifier's bound variables
        // into the atom-freedom gate. This predicate feeds paper-certificate
        // contexts (e.g. MBQI instance evaluation treating "is a definition"
        // as "instance true"), where accepting bound-var arithmetic atoms
        // resurrects the popcount wrong-SAT (#8969: `logic_*` div/mod
        // definitions bypass the div/mod guard via
        // `is_quantifier_consumer_completion_arith_uf_symbol`). The completeness case that
        // needs bound-var atoms (spec-fn definitions over BV) goes through
        // `quantifier_is_pointwise_materializable_uf_definition` on the
        // model-backed leg instead.
        self.uf_definition_supported_by_completion(args[0], args[1])
            || self.uf_definition_supported_by_completion(args[1], args[0])
    }

    /// True when `body` is a bare POSITIVE application of a free Boolean-UF to
    /// exactly the bound variables — `∀v⃗. f(v⃗)` — the spec-fn axiom that pins a
    /// predicate identically true over its whole domain.
    ///
    /// This is exactly the constant UF-definition `∀v⃗. f(v⃗) = true` written
    /// without the redundant `= true` (Verus lowers a `#[spec] fn` whose body is
    /// the literal `true`, e.g. `cintf`, to precisely this shape). The
    /// `= <constant>` recognizers (`quantifier_is_constant_uf_definition` /
    /// `quantifier_is_uf_definition`) both require an `=`-headed body, so they
    /// never match a bare-predicate body and every instance `f(c⃗)` was left
    /// `Unknown`, over-rejecting a genuinely valid model in the MBQI soundness
    /// gate (the choose-over-empty-nat-set counterexample, ay #8123 sibling /
    /// deductive-checks choose.rs cast case).
    ///
    /// SOUNDNESS: `f` is a free (completable, non-selector/constructor) UF
    /// applied to exactly the distinct bound variables, so `f := λv⃗. true`
    /// materializes pointwise without disturbing any other symbol; the asserted
    /// `forall` universally-instantiates to force `f(c⃗)` true for every ground
    /// tuple `c⃗`. This is only ever consulted after
    /// `assertions_force_false(ground_instance)` (mbqi.rs:503) has already ruled
    /// out any ground literal forcing `f(c⃗)` false, and only on the model-eval
    /// `Unknown` (unpinned) leg — so certifying `True` can neither mask a real
    /// counterexample nor produce a wrong-unsat. A negative body (`(not (f v))`)
    /// or a connective body is rejected here (its head symbol is not a
    /// completable UF), matching the `= true`-only intent.
    ///
    /// SCOPE: restricted to bound variables over INTERPRETED sorts (Int, Real,
    /// BitVec, Bool — a fixed nonempty domain over which `f≡true` is a genuine
    /// total definition). Bound variables over an UNINTERPRETED (or datatype)
    /// sort are deliberately excluded so this stays inside the standing policy
    /// that a `forall` over an uninterpreted sort which neither E-matching nor
    /// CEGQI can handle degrades to `unknown` rather than `sat` (#2865 /
    /// enumerative-no-ground-terms #5042): such a domain may be empty and the
    /// solver reports honest incompleteness there. Excluding those sorts only
    /// narrows an already-sound certification (fires strictly less), so it
    /// cannot introduce a wrong verdict.
    fn quantifier_is_total_true_bool_predicate(
        &self,
        vars: &[(String, Sort)],
        body: TermId,
    ) -> bool {
        if self.ctx.terms.sort(body) != &Sort::Bool {
            return false;
        }
        // Interpreted-sort bound variables only (see SCOPE above).
        if vars.iter().any(|(_, sort)| {
            matches!(sort, Sort::Uninterpreted(_) | Sort::Datatype(_))
                || self.binder_sort_is_datatype(sort)
        }) {
            return false;
        }
        let TermData::App(f, args) = self.ctx.terms.get(body) else {
            return false;
        };
        if args.is_empty()
            || !is_mbqi_completable_uf_symbol(f.name())
            || self.symbol_is_datatype_selector_or_constructor(f.name())
        {
            return false;
        }
        // Head args: exactly the bound variables, each used once (a total
        // definition), mirroring `quantifier_is_pointwise_materializable_uf_definition`.
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        let mut seen: HashSet<String> = HashSet::default();
        for &arg in args {
            let TermData::Var(name, _) = self.ctx.terms.get(arg) else {
                return false;
            };
            if !bound.contains(name) || !seen.insert(name.clone()) {
                return false;
            }
        }
        seen.len() == vars.len()
    }

    /// True when `quant` is a UF-definition `forall v⃗. f(v⃗) = rhs` (either
    /// orientation) that can be MATERIALIZED POINTWISE over any model without
    /// disturbing other symbols: `f := λv⃗. eval(rhs)`.
    ///
    /// Requirements:
    /// - the head applies a completable (free, non-selector/constructor) UF to
    ///   exactly the bound variables, each used once (a total definition);
    /// - the rhs never applies `f` itself (no recursion — a recursive
    ///   "definition" is a fixpoint constraint, not a pointwise assignment);
    /// - the rhs is interpreted-pure in the bound variables
    ///   (`body_is_pure_arith_bool`): any other uninterpreted application in it
    ///   is bound-var-free, i.e. a fixed constant under the model, so the
    ///   materialization does not depend on symbols it redefines.
    ///
    /// Used by the MODEL-BACKED certificate leg
    /// (`quantifiers_supported_by_uf_completion_given_sat`): with a genuine
    /// validated ground model whose e-matching instantiation coverage is
    /// complete, redefining `f` this way preserves every ground assertion
    /// (the model already agrees with the definition at every ground
    /// application) and satisfies the `forall` by construction. The recursive
    /// popcount-style shape (#8969) is rejected by the no-self-application
    /// rule.
    pub(in crate::executor) fn quantifier_is_pointwise_materializable_uf_definition(
        &self,
        quant: TermId,
    ) -> bool {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return false;
        };
        let TermData::App(eq, sides) = self.ctx.terms.get(*body) else {
            return false;
        };
        if eq.name() != "=" || sides.len() != 2 {
            return false;
        }
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        self.pointwise_definition_eq_head(vars, &bound, sides[0], sides[1], &[])
            .or_else(|| self.pointwise_definition_eq_head(vars, &bound, sides[1], sides[0], &[]))
            .is_some()
    }

    /// GENERALIZED pointwise-materializable UF-definition recognizer (rank-9
    /// step 3). Returns the DEFINED head symbol when `quant` is
    ///
    /// - an unguarded definition `forall v⃗. f(v⃗) = rhs` (either orientation;
    ///   exactly [`Self::quantifier_is_pointwise_materializable_uf_definition`]), or
    /// - a GUARDED definition `forall v⃗. guard(v⃗) => f(v⃗) = rhs`, matched in
    ///   both its raw `(=> guard (= …))` form and the constructed-`or` form
    ///   `(or g₁ … gₖ (= …))` (`mk_implies` lowers `a => b` to `(or (not a) b)`),
    ///   where EVERY non-equation disjunct (the guard residue) is
    ///   interpreted-pure in the bound variables and `f`-free, exactly like
    ///   `rhs`.
    ///
    /// # Why the guarded shape materializes pointwise
    ///
    /// Under a genuine ground model with FULL E-matching instantiation
    /// coverage (enforced at the certificate construction site), extend the
    /// model by
    ///
    /// ```text
    /// f := λv⃗. if v⃗ is a covered ground application point -> model value
    ///          else if guard(v⃗)                            -> eval(rhs(v⃗))
    ///          else                                         -> any fixed value
    /// ```
    ///
    /// - Ground assertions are untouched: `f`'s value at every ground
    ///   application point is preserved.
    /// - The quantifier holds at covered points because its E-matching
    ///   instance `guard(c⃗) => f(c⃗) = rhs(c⃗)` sits in the validated ground
    ///   core, and at uncovered points by construction (guard-true points take
    ///   `eval(rhs)`; guard-false points are unconstrained by the definition).
    /// - `guard` and `rhs` are interpreted-pure and `f`-free, so their
    ///   evaluation only reads interpreted operators and OTHER symbols at
    ///   bound-var-free (ground, hence model-pinned) applications — never the
    ///   values this materialization is choosing.
    ///
    /// The argument is PER SYMBOL: two definitional quantifiers for the same
    /// head can clash at an uncovered point (`v ≥ 0 => f(v)=1` and
    /// `v ≤ 0 => f(v)=2` clash at 0), so the certificate site must also
    /// require pairwise-distinct heads — which is why this returns the head
    /// symbol instead of a bare bool. When in doubt this returns `None`
    /// (e.g. a guard that applies a UF to the binder, a recursive rhs, a
    /// selector/constructor head, or two candidate equation disjuncts).
    pub(in crate::executor) fn pointwise_materializable_uf_definition_head(
        &self,
        quant: TermId,
    ) -> Option<String> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return None;
        };
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        match self.ctx.terms.get(*body) {
            // Unguarded: forall v⃗. lhs = rhs.
            TermData::App(eq, sides) if eq.name() == "=" && sides.len() == 2 => self
                .pointwise_definition_eq_head(vars, &bound, sides[0], sides[1], &[])
                .or_else(|| {
                    self.pointwise_definition_eq_head(vars, &bound, sides[1], sides[0], &[])
                }),
            // Guarded, constructed form: forall v⃗. (or g₁ … gₖ (= head rhs)).
            TermData::App(orsym, disjuncts) if orsym.name() == "or" => {
                let mut found: Option<String> = None;
                for (i, &d) in disjuncts.iter().enumerate() {
                    let TermData::App(eq, sides) = self.ctx.terms.get(d) else {
                        continue;
                    };
                    if eq.name() != "=" || sides.len() != 2 {
                        continue;
                    }
                    let guards: Vec<TermId> = disjuncts
                        .iter()
                        .enumerate()
                        .filter_map(|(j, &g)| (j != i).then_some(g))
                        .collect();
                    let head = self
                        .pointwise_definition_eq_head(vars, &bound, sides[0], sides[1], &guards)
                        .or_else(|| {
                            self.pointwise_definition_eq_head(
                                vars, &bound, sides[1], sides[0], &guards,
                            )
                        });
                    if let Some(head) = head {
                        if found.is_some() {
                            // Two definitional equation disjuncts: ambiguous —
                            // conservatively not a definition. (Structurally
                            // unreachable — a second UF-headed equation is an
                            // impure guard residue for the first — but kept
                            // explicit.)
                            return None;
                        }
                        found = Some(head);
                    }
                }
                found
            }
            // Guarded, raw-implication form (internal producers may keep `=>`).
            TermData::App(impl_sym, args) if impl_sym.name() == "=>" && args.len() == 2 => {
                let TermData::App(eq, sides) = self.ctx.terms.get(args[1]) else {
                    return None;
                };
                if eq.name() != "=" || sides.len() != 2 {
                    return None;
                }
                // A guard `g` is interpreted-pure/f-free iff `(not g)` is, so
                // passing the positive guard is equivalent.
                let guards = [args[0]];
                self.pointwise_definition_eq_head(vars, &bound, sides[0], sides[1], &guards)
                    .or_else(|| {
                        self.pointwise_definition_eq_head(vars, &bound, sides[1], sides[0], &guards)
                    })
            }
            // Equality pushed through an ITE by Boolean preprocessing:
            // `ite(c, f(v⃗)=r₁, f(v⃗)=r₂)` is the pointwise definition
            // `f(v⃗) = ite(c, r₁, r₂)`. Both branches must independently be
            // valid definitions of the same direct head; threading `c` as a
            // guard makes the existing purity/f-freedom checks cover the
            // condition as well (the else guard `not c` has identical symbol
            // dependencies).
            TermData::Ite(condition, then_branch, else_branch) => {
                let branch_head = |branch: TermId| {
                    let TermData::App(eq, sides) = self.ctx.terms.get(branch) else {
                        return None;
                    };
                    if eq.name() != "=" || sides.len() != 2 {
                        return None;
                    }
                    let guards = [*condition];
                    self.pointwise_definition_eq_head(vars, &bound, sides[0], sides[1], &guards)
                        .or_else(|| {
                            self.pointwise_definition_eq_head(
                                vars, &bound, sides[1], sides[0], &guards,
                            )
                        })
                };
                let then_head = branch_head(*then_branch)?;
                let else_head = branch_head(*else_branch)?;
                (then_head == else_head).then_some(then_head)
            }
            _ => None,
        }
    }

    /// Shared matcher for one orientation of a (possibly guarded) pointwise
    /// UF-definition equation: `head` must apply a completable free UF to
    /// exactly the distinct bound variables; `rhs` and every term in `guards`
    /// must be interpreted-pure in the bound variables and must not apply the
    /// head symbol anywhere. Returns the head symbol name on success.
    fn pointwise_definition_eq_head(
        &self,
        vars: &[(String, Sort)],
        bound: &HashSet<String>,
        head: TermId,
        rhs: TermId,
        guards: &[TermId],
    ) -> Option<String> {
        let TermData::App(f, args) = self.ctx.terms.get(head) else {
            return None;
        };
        if args.is_empty()
            || !is_mbqi_completable_uf_symbol(f.name())
            || self.symbol_is_datatype_selector_or_constructor(f.name())
        {
            return None;
        }
        // Head args: exactly the bound variables, each used once.
        let mut seen: HashSet<String> = HashSet::default();
        for &arg in args {
            let TermData::Var(name, _) = self.ctx.terms.get(arg) else {
                return None;
            };
            if !bound.contains(name) || !seen.insert(name.clone()) {
                return None;
            }
        }
        if seen.len() != vars.len() {
            return None;
        }
        // rhs: interpreted-pure in the bound vars, and f-free.
        if !self.body_is_pure_arith_bool(rhs, bound) || self.term_applies_symbol(rhs, f.name()) {
            return None;
        }
        // Guard residue: same discipline as rhs (interpreted-pure, f-free) so
        // the materialization can evaluate the guard without touching the
        // symbol it is defining.
        for &g in guards {
            if !self.body_is_pure_arith_bool(g, bound) || self.term_applies_symbol(g, f.name()) {
                return None;
            }
        }
        Some(f.name().to_string())
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

    /// SOUND finite-domain MBQI SAT validation (#mbqi-completeness Q2 / EPR).
    ///
    /// Returns `Some(())` ONLY when the candidate model can be soundly certified
    /// to satisfy every `forall` in `forall_quants` - i.e. the SAT is genuine.
    /// Returns `None` (fail closed) on any incompleteness so the caller keeps its
    /// conservative `Unknown`. NEVER reports a wrong SAT.
    ///
    /// Soundness rests on the EPR / finite-model-finding (Bernays-Schoenfinkel)
    /// argument: when every bound variable of every `forall` ranges over an
    /// UNINTERPRETED sort whose model universe is GENERATED ONLY BY GROUND
    /// CONSTANTS (no function symbol returns that sort applied to arguments - so
    /// no f(a), f(f(a)), ... infinite tower), the sort's domain is exactly the
    /// finite set of ground terms of that sort. Instantiating each `forall` at the
    /// full cross-product of those ground terms and evaluating every instance to a
    /// DEFINITE Bool(true) under the model is then a COMPLETE check of the
    /// universal - there are no other domain elements to falsify it. The model
    /// already satisfies the ground (quantifier-free) core (the ground solve
    /// returned SAT), so it satisfies the whole problem.
    ///
    /// This does NOT apply to interpreted infinite sorts (Int/Real/BV/Array/...),
    /// nor to uninterpreted sorts with element-producing functions, nor when any
    /// instance fails to evaluate to a concrete Bool - all of which return `None`.
    /// True when every subterm of `term` is Bool-, BitVec-, or (linear) Int-
    /// sorted and no nested quantifier occurs: the fragment where the ground
    /// solve is DECISION-COMPLETE, so a ground `Sat` carries a genuine total
    /// model with no unevaluable/fallback atoms. `Int` terms are admitted only
    /// when built from fully-model-evaluable LINEAR operators (`+ - < <= > >= =
    /// distinct` + Bool connectives + uninterpreted applications). Every other
    /// arithmetic symbol — `* / div mod abs to_real to_int is_int` — leaves the
    /// fragment, dodging the #8969 popcount wrong-SAT (a UFLIA core with
    /// div/mod can "Sat" on a model it cannot fully evaluate); pure LINEAR
    /// Int arithmetic over model-assigned variables and EUF applications IS fully
    /// evaluated, so div/mod/mul are the only unsound admissions and they are
    /// rejected here. Real/Array/Seq/String/FP-sorted subterms disqualify too.
    pub(in crate::executor) fn term_in_bv_bool_euf_lia_fragment(&self, term: TermId) -> bool {
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if !matches!(
                self.ctx.terms.sort(t),
                Sort::Bool | Sort::BitVec(_) | Sort::Int
            ) {
                return false;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if is_pure_arith_bool_symbol(sym.name())
                        && !is_evaluable_linear_symbol(sym.name())
                    {
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

    /// SAT certification for a skipped-quantifier set that is a MIX of (a)
    /// pointwise-materializable UF definitions `forall v⃗. f(v⃗) = rhs` and (b)
    /// guarded foralls `forall x. (or … G …)` whose GROUND disjunct `G` is TRUE in
    /// the returned `model`. Requires the ground core to be fully model-evaluable
    /// (linear-Int / Bool / BV / EUF — no div/mod, so the ground `Sat` is
    /// trustworthy, guarding #8969).
    ///
    /// # Why sound
    ///
    /// The ground model already satisfies the ground core (fully evaluable). Each
    /// definition is materialized pointwise `f := λv⃗. eval(rhs)` without
    /// disturbing other symbols. Each guarded forall with `eval(G, model) = true`
    /// holds for EVERY binder value, since `(or … G …)` is true once `G` is —
    /// pure propositional, independent of the binder domain OR of whether the
    /// guarded predicate is also pinned by a definition. So the model (so
    /// extended) satisfies the whole problem: the `Sat` is genuine, i.e. a real
    /// Verus counterexample rather than a heuristic. Read-only; only ever GRANTS
    /// for this shape, so it can only turn a fail-closed `Unknown` into a genuine
    /// `Sat` — never mask a proof.
    pub(in crate::executor) fn mbqi_sat_validated_definitions_plus_model_true_guards(
        &self,
        forall_quants: &[TermId],
        model: &Model,
    ) -> bool {
        if forall_quants.is_empty() {
            return false;
        }
        let ground_evaluable = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| !contains_quantifier(&self.ctx.terms, a))
            .all(|a| self.term_in_bv_bool_euf_lia_fragment(a));
        if !ground_evaluable {
            return false;
        }
        forall_quants.iter().copied().all(|q| {
            self.quantifier_is_pointwise_materializable_uf_definition(q)
                || self.is_guarded_forall_with_model_true_ground_consequent(q, model)
        })
    }

    /// True iff `quant` is `forall x⃗. (or D1 … Dn)` with some disjunct `Di` that
    /// is GROUND (mentions no bound variable), lies in the fully-evaluable LINEAR
    /// fragment, and evaluates to `true` under `model`. Then the body is true for
    /// every binder value (the true ground disjunct dominates), so the forall is
    /// satisfied by `model`. Sound by pure propositional logic — see
    /// [`Self::mbqi_sat_validated_definitions_plus_model_true_guards`].
    fn is_guarded_forall_with_model_true_ground_consequent(
        &self,
        quant: TermId,
        model: &Model,
    ) -> bool {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return false;
        };
        let bound: HashSet<String> = vars.iter().map(|(n, _)| n.clone()).collect();
        // `a => b` is stored as `(or (not a) b)`, so a guarded axiom body is `or`.
        let TermData::App(sym, args) = self.ctx.terms.get(*body) else {
            return false;
        };
        if sym.name() != "or" {
            return false;
        }
        args.iter().copied().any(|d| {
            !self.term_contains_bound_var(d, &bound)
                && self.term_in_bv_bool_euf_lia_fragment(d)
                && matches!(self.evaluate_term(model, d), EvalValue::Bool(true))
        })
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
        model: &Model,
    ) -> bool {
        let debug = std::env::var_os("AY_DEBUG_CERT").is_some();
        if forall_quants.is_empty() {
            return false;
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
        let mut pairs: Vec<(String, String, Sort)> = Vec::new();
        let mut identity_heads: HashSet<String> = HashSet::default();
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
            return false;
        }
        // Premise 2: one materialized interpretation per constrained head —
        // any symbol claimed by two roles (or by two different pairings)
        // declines.
        let mut roles: HashMap<String, LiRole> = HashMap::default();
        for (box_sym, unbox_sym, binder_sort) in &pairs {
            if roles.insert(box_sym.clone(), LiRole::BoxHead).is_some() {
                return false;
            }
            let unbox_role = LiRole::UnboxHead {
                box_sym: box_sym.clone(),
                result_sort: binder_sort.clone(),
            };
            if roles.insert(unbox_sym.clone(), unbox_role).is_some() {
                return false;
            }
        }
        for f in &identity_heads {
            if roles.insert(f.clone(), LiRole::IdentityHead).is_some() {
                return false;
            }
        }
        // Declared-symbol registry: interpreted-operator delegation to the
        // core evaluator must never catch a USER-DECLARED symbol that merely
        // shares an interpreted operator's name shape (e.g. a UF named
        // `bvfoo` — `is_interpreted_bv_symbol` matches on prefix).
        let declared: HashSet<String> = self
            .ctx
            .symbols_iter()
            .map(|(name, _)| name.clone())
            .collect();
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
                let name = sym.name().to_string();
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
                let key: LiUfKey = (name, arg_values);
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
                let name = sym.name().to_string();
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
                let key: LiUfKey = (name, arg_values);
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
                    return false;
                }
                continue;
            }
            if contains_quantifier(&self.ctx.terms, assertion) {
                // A nested quantifier (or top-level exists) is outside the
                // construction argument entirely.
                return false;
            }
            let value =
                self.left_inverse_reeval(model, &roles, &declared, &uf_table, &mut memo, assertion);
            if value != Some(LiValue::Bool(true)) {
                if debug {
                    eprintln!(
                        "CERT/left-inverse: ground assertion {assertion:?} re-evaluates to {value:?} — decline"
                    );
                }
                return false;
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
                return false;
            }
        }
        if debug {
            eprintln!("CERT/left-inverse: granted");
        }
        true
    }

    /// Evaluate every term of `terms` under the current partial `M'`;
    /// `Some(values)` iff ALL are definite (fail-closed otherwise).
    fn left_inverse_reeval_all(
        &mut self,
        model: &Model,
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
                        if self.li_symbol_is_adoptable_uf(head.name(), roles, declared) {
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
                    if self.li_symbol_is_adoptable_uf(sym.name(), roles, declared) {
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
    /// The positive `declared` requirement is the load-bearing guard: it
    /// excludes every reserved/theory symbol this predicate does not
    /// enumerate (e.g. `(_ divisible n)`), whose semantics are FIXED and must
    /// never be chosen freely. Datatype members that do appear in the
    /// declared registry are blocked mechanically by the sort gates (their
    /// argument or result sorts have no [`LiValue`] representation, so no
    /// point can ever be keyed or valued).
    fn li_symbol_is_adoptable_uf(
        &self,
        name: &str,
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
    ) -> bool {
        declared.contains(name)
            && !roles.contains_key(name)
            && !self.ctx.terms.is_skolem_symbol(name)
            && !is_pure_arith_bool_symbol(name)
            && !is_interpreted_bv_symbol(name)
    }

    /// Whether an application head delegates to the core evaluator as a PURE
    /// INTERPRETED operator (rebuilt over constant arguments): whitelisted
    /// linear-arith/Bool or BV operator, and NOT shadowed by a user
    /// declaration or Skolem (a UF named `bvfoo` must not ride the `bv*`
    /// prefix whitelist).
    fn li_symbol_is_delegable_interpreted(&self, name: &str, declared: &HashSet<String>) -> bool {
        (is_evaluable_linear_symbol(name) || is_interpreted_bv_symbol(name))
            && !declared.contains(name)
            && !self.ctx.terms.is_skolem_symbol(name)
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

    /// [`Self::term_in_bv_bool_euf_lia_fragment`] with uninterpreted-SORTED
    /// subterms additionally allowed (same operator discipline — mod/div/*
    /// still decline). The left-inverse certificate necessarily works over
    /// ground cores containing uninterpreted-sorted (boxed) terms; their
    /// values are definite `Element`s under the EUF model, and every atom the
    /// certificate's argument depends on is directly checked for definite
    /// evaluation, so the sort restriction of the strict fragment adds
    /// nothing there.
    fn term_in_bv_bool_euf_lia_or_uninterpreted_fragment(&self, term: TermId) -> bool {
        let debug = std::env::var_os("AY_DEBUG_CERT").is_some();
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

    /// Recognize `forall x:S. (= (f x) x)` (either equality orientation):
    /// single binder, `f` a non-Skolem uninterpreted unary symbol applied
    /// exactly to the bound variable. `f := id` materializes over ANY
    /// (enlarged) universe, so the shape is universe-independent once its
    /// ground applications are verified to agree with the model.
    fn unary_identity_definition_symbol(&self, quant: TermId) -> Option<String> {
        let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant) else {
            return None;
        };
        let [(var_name, _)] = vars.as_slice() else {
            return None;
        };
        let TermData::App(eq, sides) = self.ctx.terms.get(*body) else {
            return None;
        };
        if eq.name() != "=" || sides.len() != 2 {
            return None;
        }
        let recognize = |lhs: TermId, rhs: TermId| -> Option<String> {
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
            let name = f.name();
            if is_pure_arith_bool_symbol(name)
                || is_interpreted_bv_symbol(name)
                || self.ctx.terms.is_skolem_symbol(name)
            {
                return None;
            }
            Some(name.to_string())
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
    fn left_inverse_axiom_symbols(&self, quant: TermId) -> Option<(String, String, Sort)> {
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
        let recognize = |lhs: TermId, rhs: TermId| -> Option<(String, String, Sort)> {
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
            let box_name = box_sym.name();
            let unbox_name = unbox.name();
            if box_name == unbox_name
                || is_pure_arith_bool_symbol(box_name)
                || is_interpreted_bv_symbol(box_name)
                || is_pure_arith_bool_symbol(unbox_name)
                || is_interpreted_bv_symbol(unbox_name)
                || self.ctx.terms.is_skolem_symbol(box_name)
                || self.ctx.terms.is_skolem_symbol(unbox_name)
            {
                return None;
            }
            if !matches!(self.ctx.terms.sort(*inner), Sort::Uninterpreted(_)) {
                return None;
            }
            Some((
                box_name.to_string(),
                unbox_name.to_string(),
                binder_sort.clone(),
            ))
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
        uf_table: &HashMap<LiUfKey, LiValue>,
        memo: &mut HashMap<TermId, Option<LiValue>>,
        term: TermId,
        sym: Symbol,
        args: &[TermId],
    ) -> Option<LiValue> {
        let name = sym.name().to_string();
        // Constrained heads: the materialized interpretation is the ONLY
        // authority (premise 2 guarantees one role per symbol).
        if let Some(role) = roles.get(&name).cloned() {
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
                LiRole::BoxHead => Some(LiValue::Elem(LiElem::BoxPoint(name, Box::new(value)))),
                // Identity head: f := id.
                LiRole::IdentityHead => Some(value),
                // Unbox: inverse of the partner Box on its BoxPoint family,
                // designated fallback everywhere else (total by construction).
                LiRole::UnboxHead {
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
                if self.li_symbol_is_delegable_interpreted(&name, declared) {
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
                } else if self.li_symbol_is_adoptable_uf(&name, roles, declared) {
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
                    uf_table.get(&(name, arg_values)).cloned()
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
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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
    /// under the materialized interpretation. The old-model variant
    /// (`is_guarded_forall_with_model_true_ground_consequent`) must NOT be
    /// used here: `M'` reinterprets the constrained heads, so truth under the
    /// extracted model does not transfer. Note the disjunct MAY mention
    /// constrained heads (it is evaluated under their materialized
    /// interpretations) and the other disjuncts may mention anything (the
    /// true closed disjunct dominates for every binder value over any
    /// universe).
    #[allow(clippy::too_many_arguments)]
    fn left_inverse_guarded_forall_holds(
        &mut self,
        model: &Model,
        roles: &HashMap<String, LiRole>,
        declared: &HashSet<String>,
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

    pub(in crate::executor) fn mbqi_sat_validated_finite_uninterpreted_domain(
        &mut self,
        forall_quants: &[TermId],
    ) -> Option<()> {
        if forall_quants.is_empty() {
            return None;
        }
        self.last_model.as_ref()?;

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
        //    constants - NO function application returns that sort.
        let assertions = self.ctx.assertions.clone();
        if self.sort_universe_has_generating_function(&assertions, &binder_sorts) {
            return None;
        }

        // 3. Collect the GROUND terms of each binder sort: the full finite
        //    Herbrand universe (by step 2). Deliberately NO synthesized witnesses
        //    (a synthetic fresh element is not in the candidate model's domain, so
        //    the model assigns it no truth, breaking the check). The minimal-
        //    Herbrand model over the actual ground terms is a sound, complete SAT
        //    witness for the EPR fragment.
        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, &assertions);

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

        Some(())
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

    /// Decide a snapshot whose root foralls bind ONLY uninterpreted sorts,
    /// where at least one bound sort has an EMPTY ground universe (no ground
    /// term of that sort anywhere): synthesize ONE fresh witness constant per
    /// empty sort (SMT-LIB sorts are nonempty), instantiate every certified
    /// forall over the full cross-product (singleton witness for empty sorts,
    /// the complete ground Herbrand universe otherwise), and decide the
    /// resulting QUANTIFIER-FREE consequence set with a fresh isolated solve.
    ///
    /// - Sub-solve **Unsat** ⟹ `Some(Unsat)`: each instance is a sound
    ///   universal-instantiation consequence (instantiation at a fresh
    ///   constant of a nonempty sort), so UNSAT of the set refutes the
    ///   problem. Decides `∀x.p(x) ∧ ∀x.¬p(x)` over an empty universe.
    /// - Sub-solve **Sat** (with a validated model) ⟹ `Some(Sat)`: restrict
    ///   every binder sort's interpretation to the term-denoted elements. The
    ///   guards below make that restriction total: no generating function
    ///   returns a binder sort, no term of an empty sort exists outside the
    ///   witness, no composite sort smuggles one in, and the certified roots
    ///   are the ONLY quantifiers in the snapshot — so every forall is
    ///   witnessed by the full instance cross-product and every ground
    ///   assertion keeps its (quantifier-free) truth. The sub-model is
    ///   ADOPTED as `last_model` so the printed finite-universe model is the
    ///   certified one.
    /// - Anything else ⟹ `None` (caller keeps its fail-closed Unknown).
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

        // 6. Fresh isolated decide of the quantifier-free consequence set.
        let (detected, _) = self.detect_logic_category(&sub_assertions);
        let category = if matches!(detected, LogicCategory::Other) {
            fallback_category
        } else {
            detected
        };
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, sub_assertions);
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        let saved_model = self.last_model.take();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.take();
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_defer = self.defer_model_validation;
        self.defer_model_validation = false;
        let result = self.solve_for_category(category);
        // Validate an unvalidated Sat NOW, while the instance set is still
        // asserted (fill-only + full validation: can only downgrade to
        // Unknown, never mint a Sat) — the S2 fail-closed pattern.
        let result = match result {
            Ok(SolveResult::Sat) if !self.last_model_validated => {
                let saved_last_result = self.last_result.take();
                let saved_skip_model_eval = self.skip_model_eval;
                self.last_result = Some(SolveResult::Sat);
                let validated = self.finalize_sat_model_validation();
                self.last_result = saved_last_result;
                self.skip_model_eval = saved_skip_model_eval;
                validated
            }
            other => other,
        };
        self.ctx.assertions = saved_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;
        match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_validation_stats = saved_validation_stats;
                self.last_unknown_reason = saved_unknown_reason;
                self.defer_model_validation = saved_defer;
                if std::env::var_os("AY_DEBUG_CERT").is_some() {
                    eprintln!("CERT/empty-universe: UNSAT via singleton-witness instances");
                }
                Some(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                // ADOPT the validated sub-model (it carries the finite
                // universe incl. the witness and every UF value at it).
                self.last_model_validated = true;
                self.last_unknown_reason = None;
                self.defer_model_validation = false;
                if std::env::var_os("AY_DEBUG_CERT").is_some() {
                    eprintln!("CERT/empty-universe: SAT with singleton universe");
                }
                Some(SolveResult::Sat)
            }
            _ => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_validation_stats = saved_validation_stats;
                self.last_unknown_reason = saved_unknown_reason;
                self.defer_model_validation = saved_defer;
                None
            }
        }
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
    ///      ([`Self::isolated_ground_solve_is_unsat`]). UNSAT of that
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

        // Never extend a solve that is already past its deadline/interrupt.
        if self.external_stop_reason().is_some() {
            return None;
        }
        let model = self.last_model.clone()?;

        // ---- 1. Partition the snapshot; reject any non-top-level-forall
        //         quantifier occurrence (exists, Not(forall), nested, ...).
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

        // ---- 2. Class-A shape scan of every forall.
        // table symbol name -> codomain kind (Int / Bool / Real).
        let mut table_syms: HashMap<String, TableCertSort> = HashMap::default();
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
                return None;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q) else {
                return None;
            };
            // Binder domain: `Int` or `Real` only (see the Real-binder doc
            // section for why the totality argument covers both).
            if vars.len() != 1 || !matches!(vars[0].1, Sort::Int | Sort::Real) {
                return None;
            }
            let (var_name, var_sort, body) = (vars[0].0.clone(), vars[0].1.clone(), *body);
            let xdep = self.finite_table_xdep_nodes(body, &var_name);
            let mut body_syms: HashSet<String> = HashSet::default();
            self.finite_table_scan_body(
                body,
                &var_name,
                &var_sort,
                &xdep,
                &mut table_syms,
                &mut body_syms,
            )?;
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

        // ---- 3. Independent re-verification: M must make every ground
        //         original definitely true (no delegation, no completion
        //         guessing — a definite Bool(true) from the evaluator).
        for &g in &grounds {
            if !matches!(self.evaluate_term(&model, g), EvalValue::Bool(true)) {
                return None;
            }
        }

        // ---- 4. Build the finite tables from EVERY ground application of a
        //         table symbol anywhere in the snapshot.
        let tables = self.finite_table_collect(&model, snapshot, &table_syms)?;

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

            if self.finite_table_check_all(
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
            )? {
                if std::env::var_os("AY_DEBUG_CERT").is_some() {
                    eprintln!(
                        "CERT/finite-table: certified SAT ({} foralls, {} table syms)",
                        infos.len(),
                        sym_names.len()
                    );
                }
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
                return None; // all combos exhausted
            }
        }
    }

    // =====================================================================
    // (#p2-default-row) c2: n-ary bare-tuple default-row SAT certificate.
    // =====================================================================

    /// CERTIFIED SAT for quantified UFLIA snapshots in the conservative
    /// "n-ary bare-tuple + default row" class — the multi-binder
    /// generalization of CAP-1 for foralls like `∀x,y:Int. p(x,y)`.
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
    ///    ([`Self::isolated_ground_solve_is_unsat`]). UNSAT is exactly
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
            if self.ctx.terms.is_no_mbqi(q) {
                return None;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q) else {
                return None;
            };
            let (vars, body) = (vars.clone(), *body);
            if vars.is_empty()
                || vars.iter().any(|(_, s)| *s != Sort::Int)
                || contains_quantifier(&self.ctx.terms, body)
            {
                return None;
            }
            let binder_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
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
                if !self.isolated_ground_solve_is_unsat(formula, fallback_category) {
                    failed_residuals.insert(formula);
                    all_pass = false;
                    break;
                }
            }
            if all_pass {
                self.install_default_row_model(&table_syms, &tables, &defaults);
                if std::env::var_os("AY_DEBUG_CERT").is_some() {
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
            let (binders, walk_root): (HashSet<String>, TermId) = match self.ctx.terms.get(root) {
                TermData::Forall(vars, body, _) if forall_set.contains(&root) => {
                    (vars.iter().map(|(n, _)| n.clone()).collect(), *body)
                }
                _ => (HashSet::default(), root),
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

    /// Install the certified table + default interpretation into the model's
    /// EUF function tables so both the printed `(define-fun ...)` (whose else
    /// branch is the LAST row's value) and `(get-value ...)` reads agree with
    /// the certified `M'`. Real rows come first (a scan takes the first
    /// match); the synthetic final row carries the default as the else value
    /// — its argument tuple is never printed as a condition.
    fn install_default_row_model(
        &mut self,
        table_syms: &HashMap<String, (usize, TableCertSort)>,
        tables: &HashMap<String, Vec<(Vec<num_bigint::BigInt>, TableCertVal)>>,
        defaults: &HashMap<String, TableCertVal>,
    ) {
        fn int_atom(v: &num_bigint::BigInt) -> String {
            use num_traits::Zero;
            if v < &num_bigint::BigInt::zero() {
                format!("(- {})", -v.clone())
            } else {
                v.to_string()
            }
        }
        fn val_atom(v: &TableCertVal) -> String {
            match v {
                TableCertVal::Bool(b) => b.to_string(),
                TableCertVal::Int(i) => int_atom(i),
                TableCertVal::Rat(r) => format!("(/ {} {})", r.numer(), r.denom()),
            }
        }
        let Some(model) = self.last_model.as_mut() else {
            return;
        };
        let euf = model
            .euf_model
            .get_or_insert_with(ay_euf::EufModel::default);
        let mut names: Vec<&String> = table_syms.keys().collect();
        names.sort_unstable();
        for name in names {
            let Some(&(arity, _)) = table_syms.get(name) else {
                continue;
            };
            let Some(rows) = tables.get(name) else {
                continue;
            };
            let Some(default) = defaults.get(name) else {
                continue;
            };
            let mut sorted_rows: Vec<&(Vec<num_bigint::BigInt>, TableCertVal)> =
                rows.iter().collect();
            sorted_rows.sort_by(|a, b| a.0.cmp(&b.0));
            let mut table: Vec<(Vec<String>, String)> = sorted_rows
                .iter()
                .map(|(k, v)| (k.iter().map(int_atom).collect(), val_atom(v)))
                .collect();
            table.push((vec!["0".to_string(); arity], val_atom(default)));
            euf.function_tables.insert(name.clone(), table);
            euf.function_table_terms.remove(name);
            euf.function_table_conflicts.remove(name);
        }
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
                if !self.isolated_ground_solve_is_unsat(formula, category) {
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
    ) -> Option<()> {
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
        let mut infos: Vec<DtForallInfo> = Vec::with_capacity(foralls.len());
        // G-route foralls (ground-reduction; verified against M' below).
        let mut g_infos: Vec<GCertInfo> = Vec::new();
        // F3 bridge pairs (bridge-UF name, declared-selector name).
        let mut f3_pairs: Vec<(String, String)> = Vec::new();
        // F4 bodies, for the bridge-freeness soundness gate below.
        let mut f4_bodies: Vec<TermId> = Vec::new();
        for &q in &foralls {
            if self.ctx.terms.is_no_mbqi(q) {
                dt_cert_note(mode, "decline: no_mbqi forall");
                return None;
            }
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(vars, body, _) => (vars.clone(), *body),
                _ => return None,
            };
            let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

            // Route F2: DT-selector tautology (model-independent).
            if self.dt_cert_classify_f2(&var_names, body).is_some() {
                continue;
            }
            // Route F3: bridge symbolic-default closure.
            if let Some((bridge, sel)) = self.dt_cert_classify_f3(&var_names, body) {
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
                .dt_cert_scan_body(body, &var_name, &xdep, &mut table_syms, &mut body_syms)
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
        // A bridge UF must NOT also be an F4 finite-table symbol (a completion
        // conflict — one symbol, two completions).
        for b in bridge_rewrite.keys() {
            if table_syms.contains_key(b) {
                dt_cert_note(mode, "decline: symbol is both an F3 bridge and an F4 table");
                return None;
            }
        }
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
        for &g in &grounds {
            let mut memo: HashMap<TermId, TermId> = HashMap::default();
            let g2 = self.dt_cert_bridge_rewrite(g, &bridge_rewrite, &mut memo);
            if !matches!(self.evaluate_term(&model, g2), EvalValue::Bool(true)) {
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
                        key_reps.entry(key).or_insert(arg);
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
                        dt_cert_note(mode, "decline: distinct e-classes collapse to one constructor value (injectivity)");
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
                // SHADOW: log only, never flip the verdict. ON: grant.
                return match mode {
                    DtCertMode::On => Some(()),
                    DtCertMode::Shadow | DtCertMode::Off => None,
                };
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
                        match table_syms.get(name) {
                            Some(&cs) if cs != codomain => return None,
                            Some(_) => {}
                            None => {
                                table_syms.insert(name.to_string(), codomain);
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
                return false;
            }
        }
        true
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
            if args.len() == 1 {
                if matches!(self.ctx.terms.get(args[0]), TermData::Var(n, _) if n == x) {
                    return Some(sym.name().to_string());
                }
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
        match self.dt_cert_tester_value(
            model,
            gi.t,
            &gi.ctor,
            bridge_rewrite,
            tester_idx,
            sel_idx,
        )? {
            false => return Some(true), // guard false for all binders — vacuous
            true => {}
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

    /// After a re-sequencing GRANT, drop the printed function-table
    /// interpretation of every FREE completable UF that heads a top-level
    /// `forall` in `snapshot` (`logic_sum`, the bridge UFs, …). This makes those
    /// foralls DEFER-eligible in the mandated quantified-model fail-closed gate:
    /// the gate treats a forall over a function with NO printed interpretation as
    /// "the sat rests on the machinery that minted it" (here, THIS certificate,
    /// which already validated every forall against the completed M'). The
    /// candidate only solved the ground core, so its arbitrary UF DEFAULTS do not
    /// witness the universals and a blind nested re-check of them would spuriously
    /// refute a genuine model.
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
                    // Every arity>0 head that appears in a forall: a printed
                    // interpretation for ANY of them makes the forall non-defer-
                    // eligible (the gate then reconstructs that interpretation for
                    // a nested re-check whose datatype model lacks injectivity /
                    // the selector round-trip, spuriously refuting a genuine
                    // universal). GROUND evaluation of these heads uses the
                    // datatype pins / per-application values, not these tables, so
                    // ground validation is unaffected.
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
            if let Some(euf) = model.euf_model.as_mut() {
                for h in &heads {
                    euf.function_tables.remove(h);
                    euf.function_table_terms.remove(h);
                    euf.function_table_conflicts.remove(h);
                }
            }
        }
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
/// function). Used only by `body_is_pure_arith_bool` so a BV-only `forall`
/// declines the UF-completion certificate. Kept separate from
/// `is_pure_arith_bool_symbol` so the UF-detection sites that use that predicate
/// are unaffected.
fn is_interpreted_bv_symbol(name: &str) -> bool {
    name.starts_with("bv")
        || matches!(
            name,
            "concat"
                | "extract"
                | "zero_extend"
                | "sign_extend"
                | "rotate_left"
                | "rotate_right"
                | "repeat"
                | "bv2nat"
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

/// Shadow-log a DT-certificate decision (reuse of the `reject_instrument`
/// env-gated telemetry pattern). Silent when the gate is `Off`.
fn dt_cert_note(mode: DtCertMode, msg: &str) {
    if !matches!(mode, DtCertMode::Off) {
        eprintln!("c CERT/dt-mbqi-sat {msg}");
    }
}
