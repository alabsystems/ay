// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared theory solve helpers and preprocessing artifacts.
//!
//! Hosts the shared model bundle plus preprocessing outputs reused by the
//! incremental and split-loop solver entry points.

use crate::executor::mod_div_elim::{eliminate_int_mod_div, eliminate_int_mod_div_by_constant};
use crate::executor::Executor;
use crate::preprocess::{
    EqDiffVar, GuardedEqMining, NormalizeArithSom, PreprocessingPass, VariableSubstitution,
};
// #8529: Use deterministic hash maps in all builds.
use ay_arrays::ArrayModel;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_euf::EufModel;
use ay_lia::LiaModel;
use ay_lra::LraModel;
use ay_seq::SeqModel;
use ay_strings::StringModel;
use num_traits::Zero;

fn eliminate_mod_div_assertions_with_optional_sources(
    terms: &mut TermStore,
    assertions: Vec<TermId>,
    source_sets: Vec<Option<Vec<Vec<TermId>>>>,
    symbolic_divisors: bool,
) -> (Vec<TermId>, Vec<Option<Vec<Vec<TermId>>>>) {
    debug_assert_eq!(
        assertions.len(),
        source_sets.len(),
        "BUG: AUFLIA preprocessing provenance must stay aligned with assertions"
    );

    let mut rewritten_assertions = Vec::with_capacity(assertions.len());
    let mut rewritten_sources = Vec::with_capacity(source_sets.len());
    for (assertion, maybe_sources) in assertions.into_iter().zip(source_sets) {
        let mod_elim = if symbolic_divisors {
            eliminate_int_mod_div(terms, &[assertion])
        } else {
            eliminate_int_mod_div_by_constant(terms, &[assertion])
        };
        let constraint_count = mod_elim.constraints.len();
        rewritten_assertions.extend(mod_elim.constraints);
        rewritten_sources.extend(std::iter::repeat_with(|| None).take(constraint_count));
        for rewritten in mod_elim.rewritten {
            rewritten_assertions.push(rewritten);
            rewritten_sources.push(maybe_sources.clone());
        }
    }

    (rewritten_assertions, rewritten_sources)
}

fn substitutable_int_constant_term(terms: &TermStore, term: TermId) -> bool {
    if !matches!(terms.sort(term), Sort::Int) {
        return false;
    }

    match terms.get(term) {
        TermData::Var(_, _) => true,
        TermData::App(sym, args) => args.is_empty() && !sym.name().starts_with("__ay_"),
        _ => false,
    }
}

fn int_constant_const_equality(terms: &TermStore, assertion: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(sym, args) = terms.get(assertion) else {
        return None;
    };
    if sym.name() != "=" || args.len() != 2 {
        return None;
    }

    for &(var, value) in &[(args[0], args[1]), (args[1], args[0])] {
        if substitutable_int_constant_term(terms, var)
            && matches!(terms.get(value), TermData::Const(Constant::Int(_)))
        {
            return Some((var, value));
        }
    }

    None
}

fn substitute_int_const_terms(
    terms: &mut TermStore,
    replacements: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
    bound_names: &HashSet<String>,
    term: TermId,
) -> TermId {
    if replacement_visible_in_scope(terms, term, bound_names) {
        if let Some(&replacement) = replacements.get(&term) {
            return replacement;
        }
    }
    let can_cache = bound_names.is_empty();
    if can_cache {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
    }

    let result = match terms.get(term).clone() {
        TermData::Const(_) | TermData::Var(_, _) => term,
        TermData::Not(inner) => {
            let new_inner =
                substitute_int_const_terms(terms, replacements, cache, bound_names, inner);
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(cond, then_term, else_term) => {
            let new_cond =
                substitute_int_const_terms(terms, replacements, cache, bound_names, cond);
            let new_then =
                substitute_int_const_terms(terms, replacements, cache, bound_names, then_term);
            let new_else =
                substitute_int_const_terms(terms, replacements, cache, bound_names, else_term);
            if new_cond == cond && new_then == then_term && new_else == else_term {
                term
            } else {
                terms.mk_ite(new_cond, new_then, new_else)
            }
        }
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| {
                    substitute_int_const_terms(terms, replacements, cache, bound_names, arg)
                })
                .collect();
            if new_args == args {
                term
            } else {
                match sym.name() {
                    "=" if new_args.len() == 2 => terms.mk_eq_coerce(new_args[0], new_args[1]),
                    "<" if new_args.len() == 2 => terms.mk_lt(new_args[0], new_args[1]),
                    "<=" if new_args.len() == 2 => terms.mk_le(new_args[0], new_args[1]),
                    ">" if new_args.len() == 2 => terms.mk_gt(new_args[0], new_args[1]),
                    ">=" if new_args.len() == 2 => terms.mk_ge(new_args[0], new_args[1]),
                    "+" => terms.mk_add(new_args),
                    "-" => terms.mk_sub(new_args),
                    "*" => terms.mk_mul(new_args),
                    "div" if new_args.len() == 2 && int_term_is_zero(terms, new_args[1]) => {
                        terms.mk_int(num_bigint::BigInt::zero())
                    }
                    "mod" if new_args.len() == 2 && int_term_is_zero(terms, new_args[1]) => {
                        new_args[0]
                    }
                    "div" if new_args.len() == 2 => terms.mk_intdiv(new_args[0], new_args[1]),
                    "mod" if new_args.len() == 2 => terms.mk_mod(new_args[0], new_args[1]),
                    _ => {
                        let sort = terms.sort(term).clone();
                        terms.mk_app(sym, new_args, sort)
                    }
                }
            }
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|(name, value)| {
                    (
                        name.clone(),
                        substitute_int_const_terms(terms, replacements, cache, bound_names, *value),
                    )
                })
                .collect();
            let mut inner_bound_names = bound_names.clone();
            for (name, _) in &bindings {
                inner_bound_names.insert(name.clone());
            }
            let new_body =
                substitute_int_const_terms(terms, replacements, cache, &inner_bound_names, body);
            if new_bindings
                .iter()
                .zip(bindings.iter())
                .all(|((_, new_value), (_, old_value))| new_value == old_value)
                && new_body == body
            {
                term
            } else {
                terms.mk_let(new_bindings, new_body)
            }
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            let mut inner_bound_names = bound_names.clone();
            for (name, _) in &vars {
                inner_bound_names.insert(name.clone());
            }
            let new_body =
                substitute_int_const_terms(terms, replacements, cache, &inner_bound_names, body);
            let new_triggers: Vec<Vec<TermId>> = triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|&term| {
                            substitute_int_const_terms(
                                terms,
                                replacements,
                                cache,
                                &inner_bound_names,
                                term,
                            )
                        })
                        .collect()
                })
                .collect();
            if new_body == body && new_triggers == triggers {
                term
            } else if matches!(terms.get(term), TermData::Forall(..)) {
                terms.mk_forall_with_triggers(vars, new_body, new_triggers)
            } else {
                terms.mk_exists_with_triggers(vars, new_body, new_triggers)
            }
        }
        other => unreachable!("unhandled TermData variant in int-constant substitution: {other:?}"),
    };

    if can_cache {
        cache.insert(term, result);
    }
    result
}

fn int_term_is_zero(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(Constant::Int(value)) if value.is_zero())
}

fn replacement_visible_in_scope(
    terms: &TermStore,
    term: TermId,
    bound_names: &HashSet<String>,
) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => !bound_names.contains(name),
        _ => true,
    }
}

fn substitute_int_const_terms_root(
    terms: &mut TermStore,
    replacements: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
    term: TermId,
) -> TermId {
    let bound_names = HashSet::default();
    substitute_int_const_terms(terms, replacements, cache, &bound_names, term)
}

/// Per-group member cap for licensing-source augmentation (#ppp-l3).
///
/// A propagation-rewritten conjunct normally cites its own original plus a
/// handful of defining equalities; a larger set signals a pathological
/// licensing environment, and the slot falls back to `None` (the pre-L3
/// invalidation) rather than growing the downstream surface-override scan.
const MAX_AUGMENTED_SOURCE_GROUP: usize = 16;

/// Extend every existing source group with `extra` licensing sources, keeping
/// each group sorted/deduped in original-id order. `None` (fail-closed) when
/// any augmented group exceeds [`MAX_AUGMENTED_SOURCE_GROUP`].
fn augmented_source_groups(
    old_groups: &[Vec<TermId>],
    extra: &[TermId],
) -> Option<Vec<Vec<TermId>>> {
    let mut new_groups = Vec::with_capacity(old_groups.len());
    for group in old_groups {
        let mut new_group = group.clone();
        for &source in extra {
            if !new_group.contains(&source) {
                new_group.push(source);
            }
        }
        new_group.sort_by_key(|term| term.index());
        new_group.dedup();
        if new_group.len() > MAX_AUGMENTED_SOURCE_GROUP {
            return None;
        }
        new_groups.push(new_group);
    }
    Some(new_groups)
}

/// Union of the FIRST source group of each licensing definition's window
/// slot. Each group is a sufficient justification on its own, so any one is
/// a valid citation; the first is the deterministic choice. `None`
/// (fail-closed) when a definition is missing from the window or carries no
/// provenance of its own.
fn licensing_definition_sources(
    licensing: &[TermId],
    slot_by_term: &HashMap<TermId, usize>,
    slots: &[Option<Vec<Vec<TermId>>>],
) -> Option<Vec<TermId>> {
    let mut extra: Vec<TermId> = Vec::new();
    for definition in licensing {
        let &definition_slot = slot_by_term.get(definition)?;
        let definition_groups = slots.get(definition_slot)?.as_ref()?;
        let first_group = definition_groups.first()?;
        for &source in first_group {
            if !extra.contains(&source) {
                extra.push(source);
            }
        }
    }
    Some(extra)
}

/// #ppp-l3 licensing-source augmentation for the AUFLIA
/// `FlattenAnd`+`PropagateValues` fixpoint.
///
/// A slot whose assertion the pass rewrote becomes each of its existing
/// source groups EXTENDED with the sources of the defining equalities that
/// licensed the rewrite (the multi-source provenance form `proof_rewrite`
/// already consumes for surface pairing and premise re-introduction),
/// REPLACING the pre-L3 blanket invalidation. Every gap fails closed to the
/// old `None`: kill switch off, an entry without a recorded source (harvest
/// overflow), a definition absent from the window or without provenance, an
/// over-cap augmented group, or an unreplayable term shape.
fn augment_propagation_rewritten_sources(
    terms: &mut TermStore,
    propagate: &crate::preprocess::PropagateValues,
    before_values: &[TermId],
    after_values: &[TermId],
    slots: &mut [Option<Vec<Vec<TermId>>>],
) {
    debug_assert_eq!(before_values.len(), after_values.len());
    debug_assert_eq!(before_values.len(), slots.len());
    let authority = crate::quant_unit_authority::quant_unit_authority_enabled();
    let source_index = authority.then(|| propagate.entry_source_index());
    let mut slot_by_term: HashMap<TermId, usize> = HashMap::default();
    if authority {
        for (index, &term) in before_values.iter().enumerate() {
            slot_by_term.entry(term).or_insert(index);
        }
    }
    // Plan first, write second: augmentation reads OTHER slots (the
    // licensing definitions' groups), and although the pass never rewrites a
    // defining equality, the two-phase discipline makes the no-feedback
    // property structural.
    let mut planned: Vec<(usize, Option<Vec<Vec<TermId>>>)> = Vec::new();
    for (index, (&before, &after)) in before_values.iter().zip(after_values.iter()).enumerate() {
        if before == after {
            continue;
        }
        let plan = source_index.as_ref().and_then(|source_index| {
            let mut visited: HashSet<TermId> = HashSet::default();
            let mut licensing: Vec<TermId> = Vec::new();
            propagate.collect_licensing_source_assertions(
                terms,
                source_index,
                before,
                &mut visited,
                &mut licensing,
            )?;
            if licensing.is_empty() {
                return None;
            }
            let extra = licensing_definition_sources(&licensing, &slot_by_term, slots)?;
            let old_groups = slots.get(index)?.as_ref()?;
            augmented_source_groups(old_groups, &extra)
        });
        planned.push((index, plan));
    }
    for (index, plan) in planned {
        slots[index] = plan;
    }
}

/// Collect the defining assertions licensing an int-constant substitution of
/// `term`: every `replacements` key occurring in `term`, mapped through
/// `definition_of`. Occurrences under shadowing binders over-approximate,
/// which keeps the licensing claim true (extra authored premises never
/// weaken an entailment). `None` (fail-closed) on a key without a recorded
/// definition or an unknown term shape.
fn collect_used_int_const_definitions(
    terms: &TermStore,
    replacements: &HashMap<TermId, TermId>,
    definition_of: &HashMap<TermId, TermId>,
    term: TermId,
) -> Option<Vec<TermId>> {
    let mut definitions: Vec<TermId> = Vec::new();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !visited.insert(current) {
            continue;
        }
        if replacements.contains_key(&current) {
            let definition = definition_of.get(&current).copied()?;
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
            continue;
        }
        match terms.get(current) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
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
            _ => return None,
        }
    }
    (!definitions.is_empty()).then_some(definitions)
}

fn substitute_int_constants_preserving_definitions(
    terms: &mut TermStore,
    assertions: &mut [TermId],
    source_sets: &mut [Option<Vec<Vec<TermId>>>],
) -> bool {
    debug_assert_eq!(
        assertions.len(),
        source_sets.len(),
        "BUG: AUFLIA preprocessing provenance must stay aligned with assertions"
    );

    let mut replacements: HashMap<TermId, TermId> = HashMap::default();
    let mut definition_of: HashMap<TermId, TermId> = HashMap::default();
    let mut blocked: HashSet<TermId> = HashSet::default();
    let mut definition_assertions: HashSet<TermId> = HashSet::default();
    for &assertion in assertions.iter() {
        let Some((var, value)) = int_constant_const_equality(terms, assertion) else {
            continue;
        };
        definition_assertions.insert(assertion);
        if blocked.contains(&var) {
            continue;
        }
        match replacements.get(&var).copied() {
            None => {
                replacements.insert(var, value);
                definition_of.insert(var, assertion);
            }
            Some(existing) if existing == value => {}
            Some(_) => {
                replacements.remove(&var);
                definition_of.remove(&var);
                blocked.insert(var);
            }
        }
    }

    if replacements.is_empty() {
        return false;
    }

    // #ppp-l3: index the window so a rewritten assertion's provenance can be
    // augmented with its licensing definitions' own source groups instead of
    // being invalidated. Definitions are skipped by the rewrite below, so
    // their positions and slots stay stable while planning.
    let authority = crate::quant_unit_authority::quant_unit_authority_enabled();
    let mut slot_by_term: HashMap<TermId, usize> = HashMap::default();
    if authority {
        for (index, &assertion) in assertions.iter().enumerate() {
            slot_by_term.entry(assertion).or_insert(index);
        }
    }

    let mut cache = HashMap::default();
    let mut changed = false;
    for index in 0..assertions.len() {
        let assertion = assertions[index];
        if definition_assertions.contains(&assertion) {
            continue;
        }
        let rewritten =
            substitute_int_const_terms_root(terms, &replacements, &mut cache, assertion);
        if rewritten != assertion {
            // Licensing-source augmentation (#ppp-l3), fail-closed to the
            // pre-L3 invalidation on any gap. See
            // `augment_propagation_rewritten_sources` for the contract.
            let planned = if authority {
                collect_used_int_const_definitions(terms, &replacements, &definition_of, assertion)
                    .and_then(|licensing| {
                        let extra =
                            licensing_definition_sources(&licensing, &slot_by_term, source_sets)?;
                        let old_groups = source_sets.get(index)?.as_ref()?;
                        augmented_source_groups(old_groups, &extra)
                    })
            } else {
                None
            };
            assertions[index] = rewritten;
            source_sets[index] = planned;
            changed = true;
        }
    }

    changed
}

/// Theory models extracted from a SAT result.
///
/// Bundles the optional model for each theory, replacing the 6 positional
/// `Option<T>` parameters to `solve_and_store_model_full`.
#[derive(Default)]
pub(in crate::executor) struct TheoryModels {
    pub(in crate::executor) euf: Option<EufModel>,
    pub(in crate::executor) array: Option<ArrayModel>,
    pub(in crate::executor) lra: Option<LraModel>,
    pub(in crate::executor) lia: Option<LiaModel>,
    pub(in crate::executor) bv: Option<ay_bv::BvModel>,
    pub(in crate::executor) fp: Option<ay_fp::FpModel>,
    pub(in crate::executor) string: Option<StringModel>,
    pub(in crate::executor) seq: Option<SeqModel>,
    /// Exact ALGEBRAIC witnesses from the NRA theory when this SAT was proven
    /// by an exact Sturm/IVT irrational-root certificate (e.g. `x*x = 2`,
    /// witness `√2`). Each entry is a variable's exact
    /// [`ay_nra::RealAlgebraicValue`] (defining square-free polynomial,
    /// 1-based root index, isolating interval — z3 `root-obj` data). Stored in
    /// the executor [`super::super::model::Model`] so variable lookup,
    /// polynomial evaluation, `(get-value)`/`(get-model)` printing and FULL
    /// model validation handle these witnesses exactly. Rational witnesses for
    /// the remaining variables arrive through the LRA model as usual. See
    /// `ay-nra::NraSolver::algebraic_model`.
    pub(in crate::executor) nra_algebraic: Vec<(TermId, ay_nra::RealAlgebraicValue)>,
    /// DT theory e-graph model exported at `Sat` by the interactive `DtSolver`
    /// lane (#mv-dt-single-source). Stored on the executor (like
    /// `nra_algebraic`) rather than in `Model`; the model printer derives ONE
    /// per-class datatype value assignment from it so `(get-model)`,
    /// `(get-value)` and the total selector definitions cannot diverge.
    pub(in crate::executor) dt: Option<ay_dt::DtModel>,
}

/// Structured LIA preprocessing output for the incremental path.
pub(in crate::executor) struct LiaPreprocessArtifacts {
    pub(in crate::executor) assertions: Vec<TermId>,
    pub(in crate::executor) var_subst: VariableSubstitution,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
    /// True if mod/div elimination introduced an UNCONSTRAINED fresh variable
    /// for a div/mod whose divisor is (possibly) zero. SAT results then require
    /// the `sat_validated_by_mod_div_or_branch` validation bypass because the
    /// model evaluator cannot replay the under-specified `(div a 0)` term
    /// (#div0).
    pub(in crate::executor) introduced_unconstrained_div_mod: bool,
}

/// Structured output from LIA assumption preprocessing (#6728).
pub(in crate::executor) struct LiaAssumptionPreprocessResult {
    /// Additional constraint assertions from mod/div elimination of assumptions.
    pub(in crate::executor) extra_assertions: Vec<TermId>,
    /// Preprocessed assumptions as `(preprocessed, original)` pairs.
    pub(in crate::executor) assumptions: Vec<(TermId, TermId)>,
}

/// Structured output from mixed arithmetic assumption preprocessing (#6737).
///
/// Bundles the preprocessed assertions, preprocessed `(rewritten, original)`
/// assumption pairs, and the `VariableSubstitution` needed for model recovery.
pub(in crate::executor) struct MixedArithAssumptionArtifacts {
    pub(in crate::executor) assertions: Vec<TermId>,
    pub(in crate::executor) assumptions: Vec<(TermId, TermId)>,
    pub(in crate::executor) var_subst: VariableSubstitution,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
}

/// Proof-facing provenance for temporary combined-theory assertion windows.
///
/// `problem_assertions` lists the temporary assertions that should still export
/// as original-problem premises. `assertion_sources` records which original
/// assertions justify each temporary term so proof rewriting can recover the
/// parsed surface syntax. Purely derived constraints (array axioms, mod/div aux
/// constraints, propagation-only consequences) are intentionally omitted.
#[derive(Clone, Default)]
pub(in crate::executor) struct ProofProblemAssertionProvenance {
    pub(in crate::executor) original_problem_assertions: Vec<TermId>,
    pub(in crate::executor) problem_assertions: Vec<TermId>,
    pub(in crate::executor) assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
}

impl Executor {
    /// Per-run gate for the inc-14 EqDiffVar pass (inc-18).
    ///
    /// `(set-option :ay-eq-diffvar true|false)` selects the pass for THIS
    /// executor instance only. Motivation (inc-18 attribution, IMC's
    /// itp-strengthened transition checks): on SAT-shaped guarded-eq
    /// queries with a nearly-free initial state the reduction DEFEATS the
    /// model search — the plain pipeline decides in ~0.2s what the reduced
    /// form cannot decide in 30s — so ay-chc's executor adapter retries an
    /// executor-unknown query once with the pass off. (The former
    /// `AY_EQ_DIFFVAR` global env kill switch is removed; the option is the
    /// only switch.)
    ///
    /// DEFAULT OFF (#eq-diffvar-uncertifiable). The pass used to default ON,
    /// and that cost verdicts in two distinct ways — both measured at this
    /// commit on the pass's own committed inc-13/inc-14 corpus
    /// (`evals/repros`), and both traced to the same mechanism: EqDiffVar runs
    /// before `GuardedEqMining` and CONSUMES the atoms that pass folds, so the
    /// cheaper and proof-reconstructible pass never fires
    /// (`preprocess.guarded_eq.folded_atoms` is non-zero only when EqDiffVar is
    /// off).
    ///
    /// 1. It destroys the MANDATORY UNSAT certificate. The pass asserts a fresh
    ///    `d` via the definitional pair `(<= d lin)` / `(>= d lin)`. Those are
    ///    solver-invented, so the reconstructed refutation's leaves for them
    ///    carry no `assume` authority, are demoted to unit `trust`, and strict
    ///    certification rejects a CORRECT refutation:
    ///   pigeon_3_2  unknown 11ms -> unsat 2ms
    ///   syn2_MIN    unknown 2335ms -> unsat 44ms
    ///
    /// 2. It blows the certification RESCUE budget. When the outer proof leans
    ///    on any trust step, `discharge_trust_steps_for_certification` re-decides
    ///    the authored problem in a fresh executor under a fixed 2000ms
    ///    wall-clock budget. That executor inherits `ctx` (so it inherits this
    ///    option) and its verdict is the certificate. On syn2_MIN the pass makes
    ///    that re-solve take 2335ms, i.e. it misses the budget by construction,
    ///    and a correct `unsat` publishes as `unknown`.
    ///
    /// (2) is why this is an option default and not a `produce_proofs_enabled()`
    /// gate. Gating on the proof tracker looks right — the tracker is on for
    /// every public decision because the UNSAT certificate is mandatory — but it
    /// is OFF inside the rescue executor, so the pass would run there and only
    /// there. The rescue must reproduce the outer solve; a gate that makes the
    /// two behave differently is the bug. The predicate has to be uniform, and
    /// the only uniform predicate is the caller's explicit request.
    ///
    /// Opting in is unchanged and still honoured: `ay-chc` writes
    /// `(set-option :ay-eq-diffvar true)` explicitly on the sessions whose
    /// workloads it has measured to benefit (`pdr_executor_backend`,
    /// `persistent`), and those keep the reduction.
    ///
    /// This is a pure restriction of an optimization, so it cannot cause a
    /// wrong verdict — only cost speed.
    fn eq_diffvar_pass_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("ay-eq-diffvar"),
            Some(ay_frontend::OptionValue::Bool(true))
        )
    }

    /// Per-run gate for the inc-13 top-level unit-clause propagation (inc-21).
    ///
    /// `(set-option :ay-unit-prop false)` disables the pass for THIS
    /// executor instance only. (The former `AY_EXEC_UNIT_PROP=0` global env
    /// kill switch is removed; the option is the only opt-out.) Mirrors
    /// `eq_diffvar_pass_enabled`: the pass had no off switch since inc-13
    /// (e36b83c flipped durationThm_2_e2_206) and must be controllable like
    /// every other preprocessing pass. Default stays ON.
    fn unit_prop_pass_enabled(&self) -> bool {
        !matches!(
            self.ctx.get_option("ay-unit-prop"),
            Some(ay_frontend::OptionValue::Bool(false))
        )
    }

    /// Preprocess LIA assertions with provenance for incremental scope handling.
    pub(in crate::executor) fn preprocess_lia_artifacts(&mut self) -> LiaPreprocessArtifacts {
        let flattened = flatten_assertions_with_sources(&self.ctx.terms, &self.ctx.assertions);
        let original_flattened: Vec<TermId> = flattened.iter().map(|(term, _)| *term).collect();
        let mut assertions = original_flattened.clone();
        let mut source_sets: Vec<Vec<TermId>> =
            flattened.into_iter().map(|(_, sources)| sources).collect();

        // Top-level unit-clause propagation (the missing simplifier piece for
        // ite-lowering triples — see benches/nip-lia-boundary in ay: a 3-assert
        // propositional core hidden among thousands of assertions cost 4227
        // theory conflicts; z3's preprocessing refutes it in 0.00s). For each
        // top-level literal L: delete ~L disjuncts from or-assertions and
        // collapse or-assertions containing L to true. An or reduced to one
        // disjunct becomes a new top-level literal — iterate to fixpoint.
        // An assertion reduced to an empty or becomes `false` and flows
        // through Tseitin/SAT, which derives UNSAT with normal core
        // attribution. Rewritten assertions take their own sources unioned
        // with the sources of every unit used (matching the var_subst
        // source-augmentation convention below).
        // Opt-out (inc-21): per-run `(set-option :ay-unit-prop false)` —
        // see `unit_prop_pass_enabled`.
        if self.unit_prop_pass_enabled() {
            const MAX_UNIT_PROP_ROUNDS: usize = 8;
            let mut rewritten_total: u64 = 0;
            let neg_of = |terms: &TermStore, t: TermId| -> Option<TermId> {
                match terms.get(t) {
                    TermData::Not(inner) => Some(*inner),
                    _ => None,
                }
            };
            for _round in 0..MAX_UNIT_PROP_ROUNDS {
                // literal -> indices of unit assertions providing it
                let mut units: HashMap<TermId, usize> = HashMap::default();
                // inner term of a `Not` unit -> unit index (for O(1)
                // contradiction lookups in both polarities)
                let mut neg_units: HashMap<TermId, usize> = HashMap::default();
                for (i, &a) in assertions.iter().enumerate() {
                    let is_or = matches!(
                        self.ctx.terms.get(a),
                        TermData::App(sym, args) if sym.name() == "or" && args.len() >= 2
                    );
                    if !is_or {
                        units.entry(a).or_insert(i);
                        if let TermData::Not(inner) = self.ctx.terms.get(a) {
                            neg_units.entry(*inner).or_insert(i);
                        }
                    }
                }
                if units.is_empty() {
                    break;
                }
                let mut changed = false;
                for i in 0..assertions.len() {
                    let a = assertions[i];
                    let args: Vec<TermId> = match self.ctx.terms.get(a) {
                        TermData::App(sym, args) if sym.name() == "or" && args.len() >= 2 => {
                            args.clone()
                        }
                        _ => continue,
                    };
                    let mut used_units: Vec<usize> = Vec::new();
                    let mut satisfied = false;
                    let mut kept: Vec<TermId> = Vec::with_capacity(args.len());
                    for &d in &args {
                        // disjunct asserted as a unit -> whole or is true
                        if let Some(&ui) = units.get(&d) {
                            if ui != i {
                                satisfied = true;
                                used_units.push(ui);
                                break;
                            }
                        }
                        // unit ~d (or d = ~u for unit u) -> drop the disjunct
                        let contradicted = match neg_of(&self.ctx.terms, d) {
                            Some(inner) => units.get(&inner).copied().filter(|&ui| ui != i),
                            None => None,
                        }
                        .or_else(|| neg_units.get(&d).copied().filter(|&ui| ui != i));
                        if let Some(ui) = contradicted {
                            used_units.push(ui);
                            continue; // disjunct deleted
                        }
                        kept.push(d);
                    }
                    if satisfied {
                        // Leave satisfied ors in place: a literal true in the
                        // assertion list confuses downstream passes on some
                        // shapes (differential-fuzz seeds degraded to unknown
                        // when ors were rewritten to true).
                        continue;
                    }
                    if kept.len() == args.len() {
                        continue;
                    }
                    let new_a = match kept.len() {
                        0 => self.ctx.terms.mk_bool(false),
                        1 => kept[0],
                        _ => self.ctx.terms.mk_or(kept),
                    };
                    if new_a != assertions[i] {
                        assertions[i] = new_a;
                        changed = true;
                        rewritten_total += 1;
                        let mut extra: Vec<TermId> = Vec::new();
                        for ui in used_units {
                            extra.extend(source_sets[ui].iter().copied());
                        }
                        source_sets[i].extend(extra);
                        source_sets[i].sort_by_key(|term| term.index());
                        source_sets[i].dedup();
                    }
                }
                if !changed {
                    break;
                }
            }
            if rewritten_total > 0 {
                self.last_statistics
                    .set_int("preprocess.unit_prop.rewritten_assertions", rewritten_total);
            }
        }

        // Difference-variable reduction (inc-14, #23 keystone's uncovered
        // half): rewrite multi-variable equality atoms to var-CONST atoms
        // over shared definitional difference variables, so guarded equality
        // CHAINS prune through single-variable bound propagation instead of
        // per-branch LIA re-derivation. Exactly equisatisfiable definitional
        // extension. Runs BEFORE variable substitution: the validated
        // pipeline order (measured on the inc-13 differential corpus:
        // 21/21 hard files decided before-subst vs 18/21 after-subst) —
        // substitution then composes with the reduced atoms, and the
        // definitional inequality PAIR survives unit-equality inlining.
        // Disabled under proof production, and OPT-IN ONLY otherwise:
        // `(set-option :ay-eq-diffvar true)` (inc-18 retry path). The default
        // is off because the reduction costs correct `unsat` verdicts two
        // different ways — see `Executor::eq_diffvar_pass_enabled` for the
        // measurements and for why the predicate cannot be
        // `produce_proofs_enabled()`.
        //
        // The second conjunct stays `is_producing_proofs()` — "did the CALLER
        // ask for a proof" — deliberately, and must NOT become
        // `produce_proofs_enabled()`. The latter reads the proof TRACKER, which
        // is on for every public decision but OFF inside the certification
        // rescue executor, so it would run the pass in the rescue and only
        // there; the rescue exists to reproduce the outer solve, so a predicate
        // that makes the two disagree is itself the defect.
        //
        // SOUNDNESS (false-SAT #eq-diffvar-congruence): the pass rewrites a
        // multi-var equality atom `(= a b)` to `(= d rhs)` over a fresh
        // difference variable `d := a - b`. That is truth-preserving for the
        // ATOM, but it removes the term-level `a = b` that EUF congruence needs
        // to fire `f(a) = f(b)`: the arithmetic solver learns `d = 0` yet never
        // propagates `a = b` to EUF, so `f(a)`/`f(b)` stay in distinct classes
        // and a genuinely-UNSAT congruence contradiction is reported SAT
        // (test_uflia_check_sat_assuming_congruence_isolation; masked in the CLI
        // only because it forces produce-proofs, which already disables the
        // pass). Skip the pass entirely when the problem contains uninterpreted
        // functions — its validated win corpus is pure-LIA guarded chains
        // (MOESI/HOLA), so restricting it to the no-UF case loses no measured
        // benefit and is provably sound (a pure restriction of an optimization
        // can never cause a wrong verdict).
        let has_uf = crate::features::StaticFeatures::collect(&self.ctx.terms, &assertions).has_uf;
        if self.eq_diffvar_pass_enabled() && !self.is_producing_proofs() && !has_uf {
            let mut dv_pass = EqDiffVar::new();
            if dv_pass.apply_with_sources(&mut self.ctx.terms, &mut assertions, &mut source_sets) {
                self.last_statistics
                    .set_int("preprocess.eq_diffvar.diff_vars", dv_pass.diff_vars);
                self.last_statistics.set_int(
                    "preprocess.eq_diffvar.rewritten_atoms",
                    dv_pass.rewritten_atoms,
                );
            }
        }

        let mut var_subst = VariableSubstitution::new();
        // Proof-interpolation knob (#campaign-rank-4): see
        // preprocess_auflia_assertions_with_proof_provenance for rationale.
        // Variable substitution rewrites assertions in place, which detaches
        // the reconstructed proof's leaves from the original assertions and
        // forces Trust-step fallbacks (fatal for proof-based interpolation).
        // See Executor::proof_no_varsubst_enabled (option or env knob).
        let skip_subst_for_proofs =
            self.produce_proofs_enabled() && self.proof_no_varsubst_enabled();
        let var_subst_changed =
            !skip_subst_for_proofs && var_subst.apply(&mut self.ctx.terms, &mut assertions);
        // Record eliminated-variable definitions for model completion at
        // finalize time (model/completion.rs).
        self.record_var_substitutions(&var_subst);
        augment_lia_source_sets_with_substitutions(
            &self.ctx.terms,
            &original_flattened,
            &mut source_sets,
            &var_subst,
        );

        if var_subst_changed {
            let mut reflattened = Vec::new();
            for (&assertion, source_set) in assertions.iter().zip(source_sets.iter()) {
                flatten_assertion_with_source(
                    &self.ctx.terms,
                    assertion,
                    source_set,
                    &mut reflattened,
                );
            }
            assertions = reflattened.iter().map(|(term, _)| *term).collect();
            source_sets = reflattened
                .into_iter()
                .map(|(_, sources)| sources)
                .collect();
        }

        // SOM normalization: distribute multiplication over addition (#4919).
        let mut som_pass = NormalizeArithSom::new();
        som_pass.apply(&mut self.ctx.terms, &mut assertions);

        // Guarded-equality mining (#23 keystone): fold equality atoms that
        // hold under every guard valuation to constants (+ paired unit
        // re-assertion) so Bool-guarded equality networks don't force
        // exponential per-branch re-derivation. Exact equivalence transform;
        // disabled under proof production and by AY_GUARDED_EQ_MINING=0.
        if !self.is_producing_proofs() {
            let mut geq_pass = GuardedEqMining::new();
            if geq_pass.apply_with_sources(&mut self.ctx.terms, &mut assertions, &mut source_sets) {
                self.last_statistics
                    .set_int("preprocess.guarded_eq.mined_rows", geq_pass.mined_rows);
                self.last_statistics
                    .set_int("preprocess.guarded_eq.folded_atoms", geq_pass.folded_atoms);
                self.last_statistics
                    .set_int("preprocess.guarded_eq.guards", geq_pass.guards_two_sided);
            }
        }

        // Lift ITEs from arithmetic expressions before Tseitin (fixes #297)
        let lifted = self.ctx.terms.lift_arithmetic_ite_all(&assertions);

        let mut preprocessed = Vec::new();
        // One proof source set per `preprocessed` slot, kept POSITIONALLY
        // aligned so the second `VariableSubstitution` round below (which
        // rewrites assertions in place without changing their count) preserves
        // each derived assertion's provenance.
        let mut preprocessed_sources: Vec<Vec<TermId>> = Vec::new();
        let mut introduced_unconstrained_div_mod = false;
        for (&assertion, source_set) in lifted.iter().zip(source_sets.iter()) {
            let mut normalized_sources = source_set.clone();
            normalized_sources.sort_by_key(|term| term.index());
            normalized_sources.dedup();

            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            introduced_unconstrained_div_mod |= mod_elim.introduced_unconstrained_div_mod;
            for derived in mod_elim.constraints.into_iter().chain(mod_elim.rewritten) {
                preprocessed.push(derived);
                preprocessed_sources.push(normalized_sources.clone());
            }
        }

        // #8736 completeness: re-run variable substitution over the
        // mod/div-eliminated assertions.
        //
        // Constant-divisor elimination rewrites `(= (mod x k) c)` into a fresh
        // remainder var `r` with the decomposition `x = k*q + r ∧ 0 ≤ r < |k|`
        // plus a separate unit `(= r c)`. Because elimination runs AFTER the
        // first `VariableSubstitution` pass (above), neither that `r = c` unit
        // NOR the decomposition's definition of the dividend `x` is ever folded:
        // `x` stays a solver variable ranging over its original (often wide) box
        // while `x = k*q + r` ties it to the fresh quotient `q`. The LP
        // relaxation of that coupling drifts and trips the branch-and-bound
        // oscillation guard (`check_split_oscillation`), so a genuinely UNSAT
        // problem (e.g. the #8736 ring cascade: `x ≡ 0 (mod 3)` over a 16-bit
        // carry chain forced to residue 1) is abandoned as `incomplete`.
        //
        // Folding `r = c` ALONE is not enough — the dividend `x` must also be
        // eliminated (`x → k*q + c`) so the search runs in quotient space, where
        // the box is tight and divisibility is implicit. Both eliminations are
        // exactly what `VariableSubstitution` performs on `x = k*q + r` and
        // `r = c`, so we simply run it a second time on the eliminated set,
        // REUSING the existing `var_subst` accumulator so model recovery
        // (`recover_substituted_lia_values`) restores the eliminated user
        // variables from the quotient/remainder model.
        //
        // SOUND (equisatisfiable — cannot flip a verdict): every substitution is
        // a top-level defining equality `v = e` (with `v` not in `e`), which
        // holds in every model, so inlining it changes no assertion's truth;
        // conflicting definitions are left in place and refute as before. This
        // is the same transform already trusted for the first-round pass.
        // `VariableSubstitution::apply` rewrites in place (defining equalities
        // collapse to reflexive tautologies, the assertion count is unchanged),
        // so `preprocessed_sources` stays positionally aligned.
        //
        // Gated under `!produce_proofs_enabled()` (like the `EqDiffVar` and
        // `GuardedEqMining` passes above): this round inlines the mod/div
        // decomposition and dissolves the rewritten `(= r c)` mod-result
        // assertions (which the proof reconstructor maps back to the original
        // `(= (mod x k) c)` premises), so running it under proof production would
        // detach the proof's `assume` leaves from the original mod assertions and
        // force extra trust steps (#6759). Completeness — not soundness — is what
        // is traded off under proofs, so this only affects how many `incomplete`
        // results a proof-producing run reports, never a verdict.
        if !self.is_producing_proofs() {
            // Clear the first round's substitution cache: reusing `var_subst`
            // adds new definitions (e.g. `x -> k*q + c`) to the map, but the
            // cache memoizes the OLD map (where `x` mapped to itself), so without
            // a reset the second `apply` would return stale, unsubstituted terms.
            var_subst.reset();
            let changed = var_subst.apply_with_sources(
                &mut self.ctx.terms,
                &mut preprocessed,
                &mut preprocessed_sources,
            );
            if changed {
                // Record the newly eliminated definitions for model completion at
                // finalize time (model/completion.rs), mirroring the first-round
                // `record_var_substitutions` call above.
                self.record_var_substitutions(&var_subst);
            }
        }

        let mut assertion_sources: HashMap<TermId, Vec<Vec<TermId>>> = HashMap::default();
        for (&assertion, source_set) in preprocessed.iter().zip(preprocessed_sources.iter()) {
            let entry = assertion_sources.entry(assertion).or_default();
            if !entry.contains(source_set) {
                entry.push(source_set.clone());
            }
        }

        LiaPreprocessArtifacts {
            assertions: preprocessed,
            var_subst,
            assertion_sources,
            introduced_unconstrained_div_mod,
        }
    }

    /// Preprocess LIA assumptions through the same normalization family as assertions (#6728).
    ///
    /// Applies the assertion-derived `VariableSubstitution` to each assumption,
    /// then runs SOM normalization, ITE lifting, and mod/div elimination.
    /// Returns `(preprocessed, original)` pairs plus any extra constraint assertions
    /// generated by mod/div elimination.
    pub(in crate::executor) fn preprocess_lia_assumptions(
        &mut self,
        assumptions: &[TermId],
        var_subst: &mut VariableSubstitution,
    ) -> LiaAssumptionPreprocessResult {
        let mut extra_assertions = Vec::new();
        let mut result_assumptions = Vec::new();

        for &original in assumptions {
            // Apply assertion-derived substitutions (e.g., y -> (+ x 1))
            let substituted = var_subst.apply_to_term(&mut self.ctx.terms, original);

            // SOM normalization
            let mut som_terms = vec![substituted];
            let mut som_pass = NormalizeArithSom::new();
            som_pass.apply(&mut self.ctx.terms, &mut som_terms);
            let normalized = som_terms[0];

            // ITE lifting
            let lifted = self.ctx.terms.lift_arithmetic_ite(normalized);

            // mod/div elimination: constraints define aux vars (permanent),
            // rewritten term is the preprocessed assumption (temporary)
            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[lifted]);
            extra_assertions.extend(mod_elim.constraints);
            let final_assumption = mod_elim.rewritten.into_iter().next().unwrap_or(lifted);

            result_assumptions.push((final_assumption, original));
        }

        LiaAssumptionPreprocessResult {
            extra_assertions,
            assumptions: result_assumptions,
        }
    }

    /// Preprocess mixed arithmetic assumptions through the full LIA normalization
    /// family (#6737).
    ///
    /// Wrapper around [`preprocess_lia_artifacts`] + [`preprocess_lia_assumptions`]
    /// for combined-theory assumption routes (LIRA, AUFLIA, AUFLIRA). Temporarily
    /// replaces `self.ctx.assertions` with the provided slice to reuse the same
    /// preprocessing pipeline that dedicated QF_LIA uses.
    pub(in crate::executor) fn preprocess_mixed_arith_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> MixedArithAssumptionArtifacts {
        // Temporarily install the caller's assertions for preprocess_lia_artifacts()
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions.to_vec());

        let mut artifacts = self.preprocess_lia_artifacts();

        // Restore original assertions
        self.ctx.assertions = saved_assertions;

        // Preprocess assumptions using the assertion-derived substitution
        let assume_result = self.preprocess_lia_assumptions(assumptions, &mut artifacts.var_subst);

        // Merge constraint assertions from mod/div elimination of assumptions
        artifacts.assertions.extend(assume_result.extra_assertions);

        MixedArithAssumptionArtifacts {
            assertions: artifacts.assertions,
            assumptions: assume_result.assumptions,
            var_subst: artifacts.var_subst,
            assertion_sources: artifacts.assertion_sources,
        }
    }

    /// Preprocess mod/div-only combined assertions with proof-premise provenance.
    ///
    /// Rewritten assertions inherit the original assertion as a proof source.
    /// Auxiliary quotient/remainder constraints are derived-only and therefore
    /// excluded from problem-scope provenance.
    pub(in crate::executor) fn preprocess_mod_div_assertions_with_proof_provenance(
        &mut self,
        assertions: &[TermId],
    ) -> (Vec<TermId>, ProofProblemAssertionProvenance) {
        let mut preprocessed = Vec::new();
        let mut assertion_sources = HashMap::default();
        for &assertion in assertions {
            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            preprocessed.extend(mod_elim.constraints);
            for rewritten in mod_elim.rewritten {
                preprocessed.push(rewritten);
                push_assertion_source_set(&mut assertion_sources, rewritten, vec![assertion]);
            }
        }
        let provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &preprocessed,
            assertion_sources,
        );
        (preprocessed, provenance)
    }

    /// Preprocess UFNIA assertions without substituting UF-valued definitions.
    ///
    /// This keeps defining equalities like `n = 2` in the assertion set, but uses
    /// them to canonicalize dependent arithmetic terms. That exposes QuantifierConsumer-style
    /// `(div (* n (+ n 1)) 2)` postconditions to constant folding or the existing
    /// quotient/remainder reduction without the broader UF substitution risks from
    /// the full LIA preprocessor.
    pub(in crate::executor) fn preprocess_ufnia_assertions_with_proof_provenance(
        &mut self,
    ) -> (Vec<TermId>, ProofProblemAssertionProvenance) {
        let original_assertions = self.ctx.assertions.clone();
        let flattened = flatten_assertions_with_sources(&self.ctx.terms, &original_assertions);
        let mut preprocessed_assertions: Vec<TermId> =
            flattened.iter().map(|(term, _)| *term).collect();
        let mut source_sets: Vec<Option<Vec<Vec<TermId>>>> = flattened
            .into_iter()
            .map(|(_, sources)| {
                let mut normalized_sources = sources;
                normalized_sources.sort_by_key(|term| term.index());
                normalized_sources.dedup();
                Some(vec![normalized_sources])
            })
            .collect();

        substitute_int_constants_preserving_definitions(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
            &mut source_sets,
        );

        let mut som_pass = NormalizeArithSom::new();
        som_pass.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
        preprocessed_assertions = self
            .ctx
            .terms
            .lift_arithmetic_ite_all(&preprocessed_assertions);
        (preprocessed_assertions, source_sets) = eliminate_mod_div_assertions_with_optional_sources(
            &mut self.ctx.terms,
            preprocessed_assertions,
            source_sets,
            true,
        );

        let mut assertion_sources = HashMap::default();
        for (&assertion, maybe_sources) in preprocessed_assertions.iter().zip(source_sets.iter()) {
            let Some(source_sets) = maybe_sources else {
                continue;
            };
            for source_set in source_sets {
                push_assertion_source_set(&mut assertion_sources, assertion, source_set.clone());
            }
        }

        let provenance = ProofProblemAssertionProvenance::from_sources(
            original_assertions,
            &preprocessed_assertions,
            assertion_sources,
        );
        (preprocessed_assertions, provenance)
    }

    /// Build AUFLIA's temporary assertion window together with proof provenance.
    ///
    /// Around `PropagateValues` and the int-constant substitution, a
    /// rewritten assertion keeps provenance as a MULTI-source group — its
    /// original sources plus the licensing defining equalities' sources
    /// (#ppp-l3) — and the fixpoint's producer records are drained into the
    /// executor store for the rebuild-lane replay. Any augmentation gap
    /// fails closed to dropping that assertion's provenance (the pre-L3
    /// behaviour), and `--no-quant-unit-authority` restores the drop
    /// wholesale. Provenance stays exact for transformations whose source
    /// identity remains explicit.
    pub(in crate::executor) fn preprocess_auflia_assertions_with_proof_provenance(
        &mut self,
    ) -> (
        Vec<TermId>,
        ProofProblemAssertionProvenance,
        VariableSubstitution,
    ) {
        let original_assertions = self.ctx.assertions.clone();
        let flattened = flatten_assertions_with_sources(&self.ctx.terms, &original_assertions);
        let mut preprocessed_assertions = Vec::new();
        let mut source_sets: Vec<Option<Vec<Vec<TermId>>>> = Vec::new();

        for (assertion, sources) in flattened {
            let mut normalized_sources = sources;
            normalized_sources.sort_by_key(|term| term.index());
            normalized_sources.dedup();

            let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &[assertion]);
            let constraint_count = mod_elim.constraints.len();
            preprocessed_assertions.extend(mod_elim.constraints);
            source_sets.extend(std::iter::repeat_with(|| None).take(constraint_count));
            for rewritten in mod_elim.rewritten {
                preprocessed_assertions.push(rewritten);
                source_sets.push(Some(vec![normalized_sources.clone()]));
            }
        }

        // #7890: Apply VariableSubstitution to AUFLIA assertions.
        // QF_ALIA benchmarks (ios_*, pointer-safe-*, qlock-*) contain many direct
        // equalities like (= e_0 (+ i 1)) and (= a_9 (store a_6 e_7 e_8)) that
        // can be eliminated by inlining. Without this, the DPLL(T) refinement loop
        // oscillates: the theory keeps finding UNSAT via contradictory_variable_bounds
        // but the SAT solver never converges because it must case-split on hundreds
        // of redundant disequalities from un-substituted variables.
        //
        // This is safe because VariableSubstitution tracks its substitution map,
        // and model recovery (recover_substituted_lia_values) restores eliminated
        // variable values at SAT time. The same pattern is used in the LIA path
        // (preprocess_lia_artifacts) and the assumption AUFLIA path
        // (preprocess_mixed_arith_assumptions).
        //
        // NOTE: This is distinct from substitute_store_flat_equalities (#7024),
        // which is NOT safe here because it removes array defining equalities
        // without tracking substitutions for model recovery.
        // Use new_skip_arrays() because array variable substitutions remove
        // defining equalities like (= b (store a i v)) that the deferred
        // postprocessing model validator needs. Int/Real/Bool substitutions
        // are safe because recover_substituted_lia_values handles model recovery.
        //
        // Gate on UF absence: when uninterpreted functions are present (QF_UFLIA,
        // QF_AUFLIA), substitutions like `result -> (wrapping_add_u8 a b)` push UF
        // applications into arithmetic contexts. The LIA solver can no longer
        // link `result = wrapping_add_u8(a,b)` via EUF because the defining
        // equality is gone, causing Unknown on otherwise-solvable formulas
        // (#7884 carry chain SAT variant). QF_ALIA benchmarks — the target of
        // this optimization — have no UF applications, so this gate is safe.
        let features =
            crate::features::StaticFeatures::collect(&self.ctx.terms, &preprocessed_assertions);
        let mut var_subst = VariableSubstitution::new_skip_arrays();
        // Proof-interpolation knob (#campaign-rank-4): variable substitution
        // rewrites assertions in place, which invalidates proof provenance and
        // forces Trust-step fallbacks in the reconstructed resolution proof.
        // The knob skips the pass when proofs are requested so the proof's
        // Assume leaves stay aligned with the original assertions (required
        // for proof-based Craig interpolation). See
        // Executor::proof_no_varsubst_enabled (option or env knob).
        let skip_subst_for_proofs =
            self.produce_proofs_enabled() && self.proof_no_varsubst_enabled();
        if features.has_uf {
            // #qfuflia-const-subst: full substitution stays gated off with UF
            // present (#7884), but VAR := CONSTANT folds are always safe (no
            // UF application moves anywhere) and are exactly the preprocessing
            // z3 applies to the SMT-COMP xs family's fact blocks.
            var_subst = VariableSubstitution::new_constants_only();
        }
        // Substitution runs in BOTH the UF and no-UF configurations (with the
        // constants-only substituter selected above when UF is present); only
        // the proof-provenance knob skips it.
        if !skip_subst_for_proofs {
            let var_subst_changed =
                var_subst.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
            // Record eliminated-variable definitions for model completion at
            // finalize time (model/completion.rs).
            self.record_var_substitutions(&var_subst);
            if var_subst_changed {
                // Invalidate provenance for assertions that changed due to substitution.
                // Substituted assertions no longer correspond 1:1 to their original sources.
                let new_len = preprocessed_assertions.len();
                source_sets.resize_with(new_len, || None);
            }
        }

        // #7024: Do NOT apply substitute_store_flat_equalities in the AUFLIA
        // preprocessor. The AUFLIA path uses with_deferred_postprocessing, which
        // restores the original (unsubstituted) assertions before model validation.
        // Store-flat substitution removes defining equalities like (= v (store w i 1)),
        // so the inner solve never builds array model entries for those variables.
        // The outer model validator then cannot evaluate the original assertions and
        // degrades SAT to Unknown.
        //
        // The substitution remains in solve_array_euf() (euf.rs) where it works
        // because that path does not use deferred postprocessing — validation runs
        // on the substituted assertions directly.

        // #auflia-alias wrong-UNSAT: collapse PURE top-level array-variable aliases
        // `(= a1 a0)` (both sides Array-sorted Var). VariableSubstitution skips
        // Array sorts (new_skip_arrays), so the alias survives into the eager
        // array-axiom fixpoint below — which ranges over the WHOLE term store
        // (no QF reachability scoping) and over-relates `select`/`store` terms
        // built on BOTH names across several array (dis)equalities, learning a
        // cross-assertion array relation that holds under NO model: a spurious
        // conflict / false theorem (the arr_lia561 store-distinct + alias family,
        // e.g. `(= a1 a0) ∧ (distinct a0 (store a1 2 x)) ∧ (distinct … a0 …)`).
        // Substituting the non-canonical name by its representative is
        // equisatisfiable (a top-level `(= a b)` forces them equal in every
        // model). UNLIKE store-flat substitution this is SAFE under deferred
        // postprocessing: we RECORD each `(eliminated, representative)` pair so
        // model completion recovers the eliminated array variable as a copy of
        // its representative, and the restored original alias equality validates.
        // Soundness gate (#bug1b-alias-quant): the alias collapse is only
        // equisatisfiable for the quantifier-free `QF_AUFLIA` problems it
        // targets. Once `process_quantifiers` has instantiated/Skolemized a
        // universal, dropping a top-level `(= a c)` whose array still occurs in
        // those ground terms is NOT equisatisfiable and yields spurious UNSAT
        // (`forall x. select c x = f x` with `(= a c)` → z3 sat, ay unsat).
        // Skip the collapse when the original problem had a quantifier — a
        // completeness-only forgone simplification, never a false-accept.
        let array_alias_pairs = if self.original_problem_had_quantifiers {
            Vec::new()
        } else {
            substitute_array_var_aliases(&mut self.ctx.terms, &mut preprocessed_assertions)
        };
        if !array_alias_pairs.is_empty() {
            for (from, to) in &array_alias_pairs {
                self.recorded_var_substitutions.insert(*from, *to);
            }
            // Substitution rewrote assertions in place; their 1:1 provenance to
            // original sources no longer holds, so invalidate it (matches the
            // VariableSubstitution handling above).
            source_sets.resize_with(preprocessed_assertions.len(), || None);
        }

        // Install the post-substitution assertion window before the legacy
        // array fixpoint. Exact finite coverage must already be active when
        // generic Skolem extensionality scans this window; otherwise the
        // generic pass creates a redundant symbolic witness for recursively
        // finite nested arrays and exposes an extra, avoidable array-cell
        // equality. The owning AUFLIA route runs the same idempotent closure
        // again after every later rewrite, immediately before solving.
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, preprocessed_assertions);
        let source_backed_assertions = source_sets.len();
        let _ = self.add_finite_index_array_closure();
        let axiom_start = self.ctx.assertions.len();
        // #7890 diagnostic: instrument AUFLIA preprocess blow-up (ios/qlock/pointer-safe)
        let _diag_terms_before_fixpoint = self.ctx.terms.len();
        self.run_array_axiom_fixpoint_at(
            axiom_start,
            super::euf::ArrayAxiomMode::LazyRow2FinalCheck,
        );
        let _diag_terms_after_fixpoint = self.ctx.terms.len();
        let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();
        let _diag_axioms_post_fixpoint = generated_axioms.len();
        preprocessed_assertions = std::mem::replace(&mut self.ctx.assertions, saved_assertions);
        debug_assert!(preprocessed_assertions.len() >= source_backed_assertions);
        // Exact-closure axioms are valid generated facts, not rewrites of a
        // particular authored assertion, so they intentionally carry no proof
        // source mapping.
        source_sets.resize_with(preprocessed_assertions.len(), || None);
        let expanded_axioms = self.ctx.terms.expand_select_store_all(&generated_axioms);
        // #w11-ite-sum: an axiom whose EXPANSION folds to `true` while the
        // original did not is a select-over-store LINK the fold just erased —
        // e.g. the ROW bridge `(= (select S i) (ite (= k i) v (select A i)))`,
        // whose LHS expands into exactly its RHS. The MAIN assertions are NOT
        // expanded here, so the original `(select S i)` terms survive in them;
        // dropping the vanished axiom leaves those reads entirely unlinked
        // from the base array (observed: candidate models committing
        // `select S i = -1` next to `select A i = -3` with `i != k` forced —
        // every model incoherent, genuine Sat degraded to Unknown). Keep the
        // ORIGINAL spelling instead: the arithmetic ITE lift below
        // materializes it into guard clauses. Semantically exact (the axiom
        // is the same array tautology either way).
        let true_t = self.ctx.terms.true_term();
        let generated_axioms: Vec<TermId> = generated_axioms
            .iter()
            .zip(expanded_axioms.iter())
            .map(|(&orig, &exp)| {
                if exp == true_t && orig != true_t {
                    orig
                } else {
                    exp
                }
            })
            .collect();
        let _diag_terms_after_expand = self.ctx.terms.len();
        let _diag_axioms_post_expand = generated_axioms.len();
        preprocessed_assertions.extend(generated_axioms.iter().copied());
        source_sets.extend(std::iter::repeat_with(|| None).take(generated_axioms.len()));
        tracing::info!(
            terms_before_fixpoint = _diag_terms_before_fixpoint,
            terms_after_fixpoint = _diag_terms_after_fixpoint,
            axioms_generated = _diag_axioms_post_fixpoint,
            terms_after_expand = _diag_terms_after_expand,
            axioms_post_expand = _diag_axioms_post_expand,
            "#7890 AUFLIA preprocess checkpoint A (fixpoint + expand)"
        );

        let mut flatten = crate::preprocess::FlattenAnd::new();
        let mut propagate = crate::preprocess::PropagateValues::new();
        let mut _diag_flatten_iters = 0_usize;
        let _diag_flatten_start_terms = self.ctx.terms.len();
        let _diag_flatten_start_assertions = preprocessed_assertions.len();
        for _ in 0..100 {
            _diag_flatten_iters += 1;
            let flattened_pass = flatten_assertions_with_optional_sources(
                &self.ctx.terms,
                &preprocessed_assertions,
                &source_sets,
            );
            let before_propagate: Vec<TermId> =
                flattened_pass.iter().map(|(term, _)| *term).collect();
            let mut flattened_sources: Vec<Option<Vec<Vec<TermId>>>> = flattened_pass
                .into_iter()
                .map(|(_, sources)| sources)
                .collect();
            preprocessed_assertions = before_propagate;

            let f = flatten.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
            debug_assert!(
                !f,
                "FlattenAnd provenance helper must mirror structural flattening before pass application"
            );

            let before_values = preprocessed_assertions.clone();
            let p = propagate.apply(&mut self.ctx.terms, &mut preprocessed_assertions);
            if p {
                // #ppp-l3 licensing-source augmentation: a propagation-
                // rewritten assertion is the original conjunct with
                // equals-replaced-by-equals licensed by harvested defining
                // equalities, so its provenance becomes each existing source
                // group EXTENDED with the licensing definitions' own source
                // groups (the multi-source form `proof_rewrite` already
                // consumes) instead of being dropped. Fail-closed: any gap —
                // kill switch off, unrecorded entry source, definition
                // without provenance in the current window, or an over-cap
                // group — declines to the old `None` for that slot.
                augment_propagation_rewritten_sources(
                    &mut self.ctx.terms,
                    &propagate,
                    &before_values,
                    &preprocessed_assertions,
                    &mut flattened_sources,
                );
            }

            source_sets = flattened_sources;

            if !p {
                break;
            }
            flatten.reset();
            propagate.reset();
        }
        // Drain the fixpoint pass's producer provenance into the executor
        // store (#ppp-l3): the rebuild-lane replay derives the rewritten
        // assumes from their authored roots exactly as for the L1 BV-route
        // drains. Kill-switch gated inside; over-cap stores are withheld
        // whole (fail-closed L1 precedent).
        self.extend_propagated_value_provenance_direct(&mut propagate);

        tracing::info!(
            iters = _diag_flatten_iters,
            terms_start = _diag_flatten_start_terms,
            terms_end = self.ctx.terms.len(),
            assertions_start = _diag_flatten_start_assertions,
            assertions_end = preprocessed_assertions.len(),
            "#7890 AUFLIA preprocess checkpoint B (flatten+propagate fixpoint)"
        );
        // #8961: Full VariableSubstitution is disabled when UF applications
        // are present, but replacing a top-level Int variable with an asserted
        // integer constant is still safe and keeps the defining equality in the
        // assertion set for model recovery. This exposes `(mod x k)` where
        // `k = 2` to the constant-divisor pass below without pushing UF terms
        // into arithmetic.
        substitute_int_constants_preserving_definitions(
            &mut self.ctx.terms,
            &mut preprocessed_assertions,
            &mut source_sets,
        );
        let _diag_lift_start_terms = self.ctx.terms.len();
        let pre_lift_assertions = preprocessed_assertions.clone();
        let (lifted, lift_budget_exhausted) = self
            .ctx
            .terms
            .lift_arithmetic_ite_all_with_status(&preprocessed_assertions);
        preprocessed_assertions = lifted;
        if lift_budget_exhausted {
            // Shannon expansion hit its new-term budget (#8414), so the lifted
            // formula still contains term-level ITEs that LRA/LIA would mark
            // unsupported (unknown). Fall back to the LINEAR definitional
            // encoding on the PRE-BLOWUP assertions: name every non-Bool ITE
            // with a fresh variable + guard clauses, then re-lift (now trivial
            // — no deep ITEs remain under arithmetic predicates). QF_ALIA
            // cs_lazy.i_*: Shannon lifted 2.4k terms into the full 200k budget
            // (15k theory atoms, solve diverges); the definitional path stays
            // at ~3k terms.
            let mut ite_defs: Vec<TermId> = Vec::new();
            let named = self
                .ctx
                .terms
                .name_non_bool_ites_all(&pre_lift_assertions, &mut ite_defs);
            preprocessed_assertions = named;
            let n_defs = ite_defs.len();
            preprocessed_assertions.extend(ite_defs);
            source_sets.resize_with(preprocessed_assertions.len(), || None);
            let (relifted, still_exhausted) = self
                .ctx
                .terms
                .lift_arithmetic_ite_all_with_status(&preprocessed_assertions);
            preprocessed_assertions = relifted;
            tracing::info!(
                ite_defs = n_defs,
                still_exhausted,
                terms_after_definitional = self.ctx.terms.len(),
                "#7890 AUFLIA ITE lift budget exhausted; applied definitional ITE naming"
            );
        }
        // #8961: PropagateValues and ITE lifting can expose constant divisors
        // after the initial mod/div pass, especially in QF_UFLIA where full
        // VariableSubstitution is disabled to preserve UF equalities. Run the
        // constant-divisor reduction again so LIA sees quotient/remainder
        // constraints instead of letting LRA mark `(mod ... k)` unsupported.
        (preprocessed_assertions, source_sets) = eliminate_mod_div_assertions_with_optional_sources(
            &mut self.ctx.terms,
            preprocessed_assertions,
            source_sets,
            false,
        );
        tracing::info!(
            terms_before = _diag_lift_start_terms,
            terms_after = self.ctx.terms.len(),
            assertions_after = preprocessed_assertions.len(),
            "#7890 AUFLIA preprocess checkpoint C (lift_arithmetic_ite)"
        );

        // #w11-ite-sum: definitional guard clauses for Int-sorted
        // CONSTANT-branch ITE terms (`(ite b 8 0)` and the bit-recombination
        // sums built from them). The Shannon lift above erases these ITEs
        // from the ASSERTIONS, but the eager/lazy array-axiom rounds keep
        // re-introducing the raw terms inside select-over-store guards like
        // `(= 31 (+ (* (ite b0 1 0) 2) ...))` — where the arithmetic lane
        // sees each ITE as an OPAQUE UNBOUNDED leaf. Without a domain link
        // LIA happily satisfies `(= 31 i)` for an index sum whose true range
        // is [0,12], every candidate model is incoherent (the Bool `b` can
        // even end the search unassigned), and the lazy AUFLIA loop degrades
        // a genuine Sat to Unknown (or, before the #w11 combiner fix,
        // manufactured a false theory conflict from the coincidence).
        // Asserting `(¬c ∨ ite = t)` and `(c ∨ ite = e)` is DEFINITIONALLY
        // TRUE for the existing ITE term in every model (a tautology of ite
        // semantics — never flips sat/unsat); propositionally the pair also
        // entails `ite ∈ {t, e}`, giving LIA tight bounds and linking the
        // SAT-level condition to the arithmetic value.
        {
            const ITE_GUARD_AXIOM_CAP: usize = 4096;
            let mut ite_guard_axioms: Vec<TermId> = Vec::new();
            let mut seen: ay_core::kani_compat::DetHashSet<TermId> =
                ay_core::kani_compat::DetHashSet::default();
            let mut guarded: ay_core::kani_compat::DetHashSet<TermId> =
                ay_core::kani_compat::DetHashSet::default();
            // `(ite c t e)` with Int-constant branches -> (c, t-value, e-value).
            let const_branch_ite =
                |terms: &TermStore,
                 t: TermId|
                 -> Option<(TermId, num_bigint::BigInt, num_bigint::BigInt)> {
                    if let TermData::Ite(c, a, b) = terms.get(t) {
                        if let (
                            TermData::Const(Constant::Int(tv)),
                            TermData::Const(Constant::Int(ev)),
                        ) = (terms.get(*a), terms.get(*b))
                        {
                            return Some((*c, tv.clone(), ev.clone()));
                        }
                    }
                    None
                };
            let mut stack: Vec<TermId> = pre_lift_assertions.clone();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                // The Int term to guard: a bare constant-branch ITE, or a
                // 2-arg product `(* <const-branch-ite> k)` / `(* k <ite>)`
                // with constant k — the LIA lane abstracts the whole PRODUCT
                // as its opaque leaf, so a guard on the inner ITE alone never
                // reaches the sum's linear form.
                let mut guard_target: Option<(
                    TermId,
                    TermId,
                    num_bigint::BigInt,
                    num_bigint::BigInt,
                )> = None; // (term, cond, then-value, else-value)
                match self.ctx.terms.get(t) {
                    TermData::App(sym, args) => {
                        if sym.name() == "*" && args.len() == 2 {
                            let (k, ite_arg) =
                                match (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1])) {
                                    (TermData::Const(Constant::Int(k)), _) => {
                                        (Some(k.clone()), args[1])
                                    }
                                    (_, TermData::Const(Constant::Int(k))) => {
                                        (Some(k.clone()), args[0])
                                    }
                                    _ => (None, args[0]),
                                };
                            if let (Some(k), Some((c, tv, ev))) =
                                (k, const_branch_ite(&self.ctx.terms, ite_arg))
                            {
                                guard_target = Some((t, c, &tv * &k, &ev * &k));
                            }
                        }
                        stack.extend(args.iter().copied());
                    }
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(c, a, b) => {
                        let (c, a, b) = (*c, *a, *b);
                        stack.push(c);
                        stack.push(a);
                        stack.push(b);
                        if let Some((c, tv, ev)) = const_branch_ite(&self.ctx.terms, t) {
                            guard_target = Some((t, c, tv, ev));
                        }
                    }
                    _ => {}
                }
                if let Some((target, c, tv, ev)) = guard_target {
                    if tv != ev
                        && matches!(self.ctx.terms.sort(target), Sort::Int)
                        && guarded.insert(target)
                        && ite_guard_axioms.len() < ITE_GUARD_AXIOM_CAP
                    {
                        let tv_term = self.ctx.terms.mk_int(tv);
                        let ev_term = self.ctx.terms.mk_int(ev);
                        let eq_t = self.ctx.terms.mk_eq(target, tv_term);
                        let eq_e = self.ctx.terms.mk_eq(target, ev_term);
                        let not_c = self.ctx.terms.mk_not(c);
                        let then_guard = self.ctx.terms.mk_or(vec![not_c, eq_t]);
                        let else_guard = self.ctx.terms.mk_or(vec![c, eq_e]);
                        ite_guard_axioms.push(then_guard);
                        ite_guard_axioms.push(else_guard);
                    }
                }
            }
            // #w11-ite-sum companion: ROW re-link for select-over-store terms
            // that SURVIVE preprocessing in the final assertion set. The eager
            // array-axiom ROW clauses for these reads are generated at
            // checkpoint A, but the expand + Shannon-lift pipeline can fold
            // them to vacuity (the lift proves the store-key guard
            // `(= k <ite-sum>)` constant and simplifies the clause against the
            // EXPANDED read while the original read term survives in the main
            // assertions) — leaving `select(store(A,k,v), i)` with NO link to
            // `select(A, i)` and every candidate model incoherent. Re-assert
            // ROW1/ROW2 here, AFTER the last folding pass, so the links reach
            // the SAT/LIA/EUF layers verbatim. Both clauses are array-theory
            // tautologies — they can never flip sat/unsat.
            let mut row_seen: ay_core::kani_compat::DetHashSet<TermId> =
                ay_core::kani_compat::DetHashSet::default();
            let mut stack: Vec<TermId> = preprocessed_assertions.clone();
            let mut visited: ay_core::kani_compat::DetHashSet<TermId> =
                ay_core::kani_compat::DetHashSet::default();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t).clone() {
                    TermData::App(sym, args) => {
                        if sym.name() == "select" && args.len() == 2 && row_seen.insert(t) {
                            if let TermData::App(inner_sym, inner_args) =
                                self.ctx.terms.get(args[0]).clone()
                            {
                                if inner_sym.name() == "store"
                                    && inner_args.len() == 3
                                    && inner_args[1] != args[1]
                                    && ite_guard_axioms.len() + 2 <= ITE_GUARD_AXIOM_CAP
                                {
                                    let (base, key, val) =
                                        (inner_args[0], inner_args[1], inner_args[2]);
                                    let sel_idx = args[1];
                                    let idx_eq = self.ctx.terms.mk_eq(key, sel_idx);
                                    let not_idx_eq = self.ctx.terms.mk_not(idx_eq);
                                    let row1_eq = self.ctx.terms.mk_eq(t, val);
                                    let row1 = self.ctx.terms.mk_or(vec![not_idx_eq, row1_eq]);
                                    let base_sel = self.ctx.terms.mk_select(base, sel_idx);
                                    let row2_eq = self.ctx.terms.mk_eq(t, base_sel);
                                    let row2 = self.ctx.terms.mk_or(vec![idx_eq, row2_eq]);
                                    let true_t = self.ctx.terms.true_term();
                                    if row1 != true_t {
                                        ite_guard_axioms.push(row1);
                                    }
                                    if row2 != true_t {
                                        ite_guard_axioms.push(row2);
                                    }
                                }
                            }
                        }
                        stack.extend(args.iter().copied());
                    }
                    TermData::Not(inner) => stack.push(inner),
                    TermData::Ite(c, a, b) => {
                        stack.push(c);
                        stack.push(a);
                        stack.push(b);
                    }
                    _ => {}
                }
            }
            if !ite_guard_axioms.is_empty() {
                tracing::debug!(
                    guards = ite_guard_axioms.len(),
                    "#w11-ite-sum: injected definitional ITE guard + ROW re-link clauses"
                );
                preprocessed_assertions.extend(ite_guard_axioms.iter().copied());
                source_sets.resize_with(preprocessed_assertions.len(), || None);
            }
        }

        if ay_core::misc_cli_flags().dump_auflia_assertions {
            let max_t = preprocessed_assertions
                .iter()
                .map(|t| t.0)
                .max()
                .unwrap_or(0);
            eprintln!("AUFLIA TERMS (0..={max_t}):");
            for idx in 0..=max_t {
                let tid = TermId(idx);
                eprintln!(
                    "  t{}: {:?}  sort={:?}",
                    idx,
                    self.ctx.terms.get(tid),
                    self.ctx.terms.sort(tid)
                );
            }
            eprintln!(
                "AUFLIA ASSERTIONS ({} preprocessed):",
                preprocessed_assertions.len()
            );
            for (i, &a) in preprocessed_assertions.iter().enumerate() {
                eprintln!("  [{}] t{}: {:?}", i, a.0, self.ctx.terms.get(a));
            }
        }

        let mut assertion_sources = HashMap::default();
        for (&assertion, maybe_sources) in preprocessed_assertions.iter().zip(source_sets.iter()) {
            let Some(source_sets) = maybe_sources else {
                continue;
            };
            for source_set in source_sets {
                push_assertion_source_set(&mut assertion_sources, assertion, source_set.clone());
            }
        }

        let provenance = ProofProblemAssertionProvenance::from_sources(
            original_assertions,
            &preprocessed_assertions,
            assertion_sources,
        );
        (preprocessed_assertions, provenance, var_subst)
    }
}

impl ProofProblemAssertionProvenance {
    pub(in crate::executor) fn from_sources(
        original_problem_assertions: Vec<TermId>,
        temporary_assertions: &[TermId],
        assertion_sources: HashMap<TermId, Vec<Vec<TermId>>>,
    ) -> Self {
        let original_problem_set: HashSet<TermId> =
            original_problem_assertions.iter().copied().collect();
        let problem_assertions = temporary_assertions
            .iter()
            .copied()
            .filter(|assertion| {
                original_problem_set.contains(assertion)
                    && assertion_sources.contains_key(assertion)
            })
            .collect();
        Self {
            original_problem_assertions,
            problem_assertions,
            assertion_sources,
        }
    }

    /// Keep the outer solve's immutable authored-premise authority while
    /// installing a narrower preprocessing window.
    ///
    /// Quantifier preprocessing freezes this authority before it merges
    /// binder towers or creates instances. Arithmetic and combined-theory
    /// preprocessors run later and build provenance relative to their current
    /// (already transformed) assertion window. Replacing the outer provenance
    /// verbatim would therefore promote those transformed terms to authored
    /// `Assume` leaves. Rebase the inner window onto the outer roots instead.
    pub(in crate::executor) fn preserving_authority_from(mut self, outer: Option<&Self>) -> Self {
        let Some(outer) = outer else {
            return self;
        };

        let authored: HashSet<TermId> = outer.original_problem_assertions.iter().copied().collect();

        let mut problem_assertions = outer.problem_assertions.clone();
        problem_assertions.retain(|assertion| authored.contains(assertion));
        for assertion in self.problem_assertions {
            if authored.contains(&assertion) && !problem_assertions.contains(&assertion) {
                problem_assertions.push(assertion);
            }
        }

        // Retain outer source paths and accept an inner source path only when
        // it is already expressed entirely in immutable authored roots. This
        // keeps surface-syntax recovery useful without making an intermediate
        // preprocessing term a source of authority.
        let mut assertion_sources = outer.assertion_sources.clone();
        for (assertion, source_sets) in self.assertion_sources {
            for source_set in source_sets {
                if source_set.iter().all(|source| authored.contains(source)) {
                    push_assertion_source_set(&mut assertion_sources, assertion, source_set);
                }
            }
        }

        self.original_problem_assertions = outer.original_problem_assertions.clone();
        self.problem_assertions = problem_assertions;
        self.assertion_sources = assertion_sources;
        self
    }

    /// Identity provenance for routes whose temporary assertion window
    /// consists of the original assertions plus purely derived constraints
    /// (e.g., generated array axioms).
    ///
    /// Each original assertion maps to itself as its sole source. Derived
    /// constraints are left unmapped so the proof bootstrap registers them
    /// as unlabeled Assumes (proof-visible but not exportable premises).
    pub(in crate::executor) fn passthrough(
        original_problem_assertions: &[TermId],
        temporary_assertions: &[TermId],
    ) -> Self {
        let mut assertion_sources = HashMap::default();
        for &assertion in original_problem_assertions {
            assertion_sources.insert(assertion, vec![vec![assertion]]);
        }
        Self::from_sources(
            original_problem_assertions.to_vec(),
            temporary_assertions,
            assertion_sources,
        )
    }
}

// Assertion flattening, store-flat substitution, and proof source tracking
// helpers are in solve_harness_helpers.rs.
use super::solve_harness_helpers::{
    augment_lia_source_sets_with_substitutions, flatten_assertion_with_source,
    flatten_assertions_with_optional_sources, flatten_assertions_with_sources,
    push_assertion_source_set,
};

// Re-export substitute_store_flat_equalities so `euf/array_fixpoint.rs` can use
// `super::super::solve_harness::substitute_store_flat_equalities`.
pub(super) use super::solve_harness_helpers::substitute_store_flat_equalities;
// Re-export substitute_array_var_aliases (#auflia-alias) for the same path.
pub(super) use super::solve_harness_helpers::substitute_array_var_aliases;

mod split_atoms;
pub(in crate::executor) use split_atoms::{
    check_split_oscillation, create_disequality_split_atoms, create_int_split_atoms,
    DisequalitySplitAtoms, SplitOscillationMap,
};

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
