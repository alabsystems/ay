// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pc-directed location splitting for SLayerCF-shaped CHC systems.
//!
//! The eldarica-misc/BV/SLayerCF instances are k-level towers of
//! `transition-i` predicates whose FIRST argument is a program counter: in
//! every rule, every predicate occurrence has `arg0` pinned to a concrete
//! constant (either a literal argument or a variable equated to a literal in
//! the clause constraint). Each level is a monolithic 46-81-way rule
//! disjunction over pc values, which blows up flat BMC/PDR on the
//! all-levels encoding.
//!
//! This transformer specializes each such predicate by its observed arg0
//! constants: predicate `P` with values `{v1..vk}` becomes clones
//! `P__ay_pc0..P__ay_pc(k-1)` with arg0 DROPPED, and every clause occurrence
//! `P(c, args...)` is rewritten to `P_c(args...)`. The clause constraint is
//! rewritten under the clause's resolved constant environment
//! (constraint-implied equalities), re-pinning only the vars that still
//! occur in a surviving predicate arg, so the dead pc variables are
//! eliminated from the split clauses rather than lingering as free
//! variables. The result is an explicit
//! control-flow graph with per-location predicates of low out-degree, on
//! which the existing pipeline (ClauseInliner / graph collapse) and the
//! BMC/tree/PDR lanes operate locally per location. Crucially, a
//! self-recursive pc-stepping predicate becomes an ACYCLIC (or
//! low-out-degree) location graph, unlocking inlining that the monolithic
//! predicate forbids.
//!
//! This is the shape-directed sibling of the general Eldarica
//! `SymbolSplitter` idea (clone on constraint-implied constant arguments in
//! every occurrence), keyed on the KNOWN SLayerCF shape (arg0 = pc).
//!
//! # Soundness (G1)
//!
//! The split is an exact re-presentation: derivations are isomorphic, and
//! clauses map 1:1 (indices recorded explicitly).
//!
//! - Safe: the model is reassembled disjunctively on the original
//!   vocabulary, `P(a0, a...) := \/_v (a0 = v /\ I_{P_v}(a...))`, and the
//!   portfolio re-validates it against the ORIGINAL clauses
//!   (`verify_model_per_rule`); failure => Unknown (fail-closed).
//! - Unsafe: counterexample steps/witness entries are remapped to original
//!   predicate ids, clause indices are translated through the recorded
//!   index map, canonical variables are shifted by one position, and the pc
//!   value is re-attached; the witness then replays against the ORIGINAL
//!   clauses (`verified_unsafe_from_witness` path); inconclusive replay =>
//!   Unknown (fail-closed).
//!
//! Kill switch: `AY_CHC_DISABLE_PC_SPLIT=1` disables the pass entirely
//! (identity transform).

use std::collections::{BTreeMap, BTreeSet};

use crate::lemma_hints::canonical_var_name;
use crate::pdr::PredicateInterpretation;
use crate::smt::SmtValue;
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformationResult, Transformer, ValidityWitness,
};

/// Per-predicate cap on distinct pc values: beyond this the predicate is
/// left unsplit (the SLayerCF levels top out around 81 values).
const MAX_PC_VALUES_PER_PREDICATE: usize = 128;

/// Problems larger than this skip the pass entirely — the target class is
/// hundreds to a few thousand clauses.
const MAX_PC_SPLIT_CLAUSES: usize = 10_000;

/// Global cap on the total number of clone predicates created.
const MAX_PC_SPLIT_TOTAL_CLONES: usize = 4_096;

/// Rounds of constraint-equality propagation when building the per-clause
/// constant environment (handles short `pc' = pc2, pc2 = 5` chains).
const CONST_ENV_PROPAGATION_ROUNDS: usize = 4;

/// Kill switch: `AY_CHC_DISABLE_PC_SPLIT=1` (any non-`0` non-empty value)
/// disables pc-directed location splitting.
pub(crate) fn pc_split_disabled_by_env() -> bool {
    // B27: CLI-owned (--chc-no-pc-split); env retired.
    !crate::ab_switches::get().pc_split
}

/// SLayerCF-shaped pc-directed location splitting transformer.
pub(crate) struct PcSplitter {
    verbose: bool,
    enabled: bool,
}

impl Default for PcSplitter {
    fn default() -> Self {
        Self::new()
    }
}

impl PcSplitter {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            enabled: !pc_split_disabled_by_env(),
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Explicit enable/disable, bypassing the environment kill switch.
    /// Used by tests so they never mutate process environment.
    #[cfg(test)]
    pub(crate) fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }
}

/// A literal pc value usable as a split key. `ChcExpr` is `Ord + Eq`, so
/// literals key `BTreeMap`s deterministically.
fn is_pc_literal(expr: &ChcExpr) -> bool {
    matches!(
        expr,
        ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Bool(_)
    )
}

/// Whether `sort` is an eligible pc sort (finite/int-like scalar).
fn is_pc_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Int | ChcSort::BitVec(_) | ChcSort::Bool)
}

/// Extract a `var -> literal` environment from the clause constraint's
/// top-level equality conjuncts, with a few rounds of var-var propagation.
fn constraint_const_env(constraint: Option<&ChcExpr>) -> Vec<(ChcVar, ChcExpr)> {
    let mut env: FxHashMap<ChcVar, ChcExpr> = FxHashMap::default();
    let Some(constraint) = constraint else {
        return Vec::new();
    };
    let conjuncts = constraint.conjuncts();

    for _ in 0..CONST_ENV_PROPAGATION_ROUNDS {
        let mut changed = false;
        for conjunct in &conjuncts {
            match conjunct {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    let (a, b) = (args[0].as_ref(), args[1].as_ref());
                    for (lhs, rhs) in [(a, b), (b, a)] {
                        let ChcExpr::Var(v) = lhs else { continue };
                        if env.contains_key(v) {
                            continue;
                        }
                        let resolved = match rhs {
                            lit if is_pc_literal(lit) => Some(lit.clone()),
                            ChcExpr::Var(w) => env.get(w).cloned(),
                            _ => None,
                        };
                        if let Some(lit) = resolved {
                            env.insert(v.clone(), lit);
                            changed = true;
                        }
                    }
                }
                // Bare boolean var conjunct: `v` means `v = true`.
                ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
                    if !env.contains_key(v) {
                        env.insert(v.clone(), ChcExpr::Bool(true));
                        changed = true;
                    }
                }
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        if v.sort == ChcSort::Bool && !env.contains_key(v) {
                            env.insert(v.clone(), ChcExpr::Bool(false));
                            changed = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }

    let mut pairs: Vec<(ChcVar, ChcExpr)> = env.into_iter().collect();
    pairs.sort();
    pairs
}

/// Resolve the concrete pc value of an occurrence's arg0 under the clause's
/// constant environment. Returns `None` when arg0 is not pinned to a literal.
fn occurrence_pc_value(arg0: &ChcExpr, env: &[(ChcVar, ChcExpr)]) -> Option<ChcExpr> {
    if is_pc_literal(arg0) {
        return Some(arg0.clone());
    }
    // arg0 is small (a var or a short pc-stepping expression like
    // `bvadd pc #x01`): substitute the environment and constant-fold.
    let folded = arg0.substitute(env).simplify_constants();
    is_pc_literal(&folded).then_some(folded)
}

/// Split plan for one predicate: sorted distinct pc values.
type SplitPlan = BTreeMap<PredicateId, Vec<ChcExpr>>;

/// Detect the SLayerCF shape and build the split plan.
///
/// A predicate is splittable when it has arity >= 1, an int-like arg0 sort,
/// at least one occurrence, EVERY occurrence (body and head, every clause)
/// resolves arg0 to a literal, and the distinct-value count is within the
/// per-level cap. The problem-level gate requires at least one splittable
/// predicate with >= 2 distinct values (otherwise splitting is pointless)
/// and bounds the total clone count.
fn detect_split_plan(problem: &ChcProblem) -> Option<SplitPlan> {
    if problem.clauses().len() > MAX_PC_SPLIT_CLAUSES {
        return None;
    }

    let mut values: BTreeMap<PredicateId, BTreeSet<ChcExpr>> = BTreeMap::new();
    let mut ineligible: Vec<bool> = problem
        .predicates()
        .iter()
        .map(|pred| pred.arg_sorts.first().is_none_or(|s| !is_pc_sort(s)))
        .collect();

    for clause in problem.clauses() {
        let env = constraint_const_env(clause.body.constraint.as_ref());
        let head_occurrence = match &clause.head {
            ClauseHead::Predicate(id, args) => Some((*id, args)),
            ClauseHead::False => None,
        };
        let occurrences = clause
            .body
            .predicates
            .iter()
            .map(|(id, args)| (*id, args))
            .chain(head_occurrence);
        for (pred_id, args) in occurrences {
            if ineligible[pred_id.index()] {
                continue;
            }
            match args
                .first()
                .and_then(|arg0| occurrence_pc_value(arg0, &env))
            {
                Some(value) => {
                    values.entry(pred_id).or_default().insert(value);
                }
                None => {
                    ineligible[pred_id.index()] = true;
                    values.remove(&pred_id);
                }
            }
        }
    }

    values.retain(|_, vals| !vals.is_empty() && vals.len() <= MAX_PC_VALUES_PER_PREDICATE);
    let total_clones: usize = values.values().map(BTreeSet::len).sum();
    let worthwhile = values.values().any(|vals| vals.len() >= 2);
    if !worthwhile || total_clones > MAX_PC_SPLIT_TOTAL_CLONES {
        return None;
    }

    Some(
        values
            .into_iter()
            .map(|(id, vals)| (id, vals.into_iter().collect()))
            .collect(),
    )
}

impl Transformer for PcSplitter {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !self.enabled {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        let Some(plan) = detect_split_plan(&problem) else {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        };

        let Some((new_problem, back_translator)) = build_split_problem(&problem, &plan) else {
            // Detection/rewrite disagreement: fail closed to identity.
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        };

        if self.verbose {
            safe_eprintln!(
                "CHC pc-split: {} predicates / {} clauses -> {} location predicates ({} split)",
                problem.predicates().len(),
                problem.clauses().len(),
                new_problem.predicates().len(),
                plan.len()
            );
        }

        TransformationResult {
            problem: new_problem,
            back_translator,
        }
    }
}

/// Build the split problem plus the back-translator. Returns `None` if any
/// occurrence of a planned predicate fails to resolve during rewrite (the
/// caller then falls back to the identity transform, fail-closed).
fn build_split_problem(
    problem: &ChcProblem,
    plan: &SplitPlan,
) -> Option<(ChcProblem, Box<dyn BackTranslator>)> {
    let mut new_problem = ChcProblem::new();
    // orig id -> value -> clone id (values sorted by construction)
    let mut clone_ids: FxHashMap<PredicateId, BTreeMap<ChcExpr, PredicateId>> =
        FxHashMap::default();
    // orig id -> passthrough id (unsplit predicates)
    let mut passthrough: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
    // new id -> (orig id, Some(pc value) for clones / None for passthrough)
    let mut reverse: FxHashMap<PredicateId, (PredicateId, Option<ChcExpr>)> = FxHashMap::default();
    let mut original_sorts: FxHashMap<PredicateId, Vec<ChcSort>> = FxHashMap::default();

    for pred in problem.predicates() {
        original_sorts.insert(pred.id, pred.arg_sorts.clone());
        if let Some(values) = plan.get(&pred.id) {
            let mut per_value = BTreeMap::new();
            for (i, value) in values.iter().enumerate() {
                let mut name = format!("{}__ay_pc{i}", pred.name);
                while new_problem.get_predicate_by_name(&name).is_some() {
                    name.push('_');
                }
                let clone_id = new_problem.declare_predicate(name, pred.arg_sorts[1..].to_vec());
                per_value.insert(value.clone(), clone_id);
                reverse.insert(clone_id, (pred.id, Some(value.clone())));
            }
            clone_ids.insert(pred.id, per_value);
        } else {
            let new_id = new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
            passthrough.insert(pred.id, new_id);
            reverse.insert(new_id, (pred.id, None));
        }
    }

    let map_occurrence = |pred_id: PredicateId,
                          args: &[ChcExpr],
                          env: &[(ChcVar, ChcExpr)]|
     -> Option<(PredicateId, Vec<ChcExpr>)> {
        if let Some(per_value) = clone_ids.get(&pred_id) {
            let value = occurrence_pc_value(args.first()?, env)?;
            let clone_id = *per_value.get(&value)?;
            Some((clone_id, args[1..].to_vec()))
        } else {
            Some((*passthrough.get(&pred_id)?, args.to_vec()))
        }
    };

    // 1:1 clause rewrite; record the transformed->original index map (a
    // clause can only vanish if `add_clause` prunes a constant-false body,
    // which the map keeps exact).
    let mut new_to_orig_clause: Vec<usize> = Vec::with_capacity(problem.clauses().len());
    for (orig_index, clause) in problem.clauses().iter().enumerate() {
        let env = constraint_const_env(clause.body.constraint.as_ref());
        let mut body_preds = Vec::with_capacity(clause.body.predicates.len());
        for (pred_id, args) in &clause.body.predicates {
            body_preds.push(map_occurrence(*pred_id, args, &env)?);
        }
        let head = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => {
                let (new_id, new_args) = map_occurrence(*pred_id, args, &env)?;
                ClauseHead::Predicate(new_id, new_args)
            }
            ClauseHead::False => ClauseHead::False,
        };
        // Rewrite the constraint by substituting the constant environment and
        // folding: every env entry `v = lit` is an equality IMPLIED by the
        // constraint, so `phi` is equivalent to `phi[env] /\ (v = lit /\ ..)`.
        // Env vars that occur in a surviving predicate arg get their pinning
        // equality conjoined back (kept as VARS so the engines' canonical
        // head-arg mapping stays strong); env vars that occur nowhere else
        // are existential with a folded-away `lit = lit` definition, so
        // dropping them preserves each clause's meaning exactly. Net effect:
        // the dead pinned-pc variables no longer litter every location
        // clause as free variables that degrade downstream engines.
        let mut constraint = clause
            .body
            .constraint
            .as_ref()
            .map(|c| c.substitute(&env).simplify_constants());
        let occurs_in_rewritten = |var: &ChcVar| {
            body_preds
                .iter()
                .flat_map(|(_, args)| args.iter())
                .chain(match &head {
                    ClauseHead::Predicate(_, args) => args.iter(),
                    ClauseHead::False => [].iter(),
                })
                .any(|arg| arg.vars().contains(var))
        };
        let pins: Vec<ChcExpr> = env
            .iter()
            .filter(|(var, _)| occurs_in_rewritten(var))
            .map(|(var, lit)| ChcExpr::eq(ChcExpr::var(var.clone()), lit.clone()))
            .collect();
        if !pins.is_empty() {
            let mut parts = vec![constraint.unwrap_or(ChcExpr::Bool(true))];
            parts.extend(pins);
            constraint = Some(ChcExpr::and_all(parts));
        }
        let body = ClauseBody::new(body_preds, constraint);
        let before = new_problem.clauses().len();
        new_problem.add_clause(HornClause::new(body, head));
        if new_problem.clauses().len() > before {
            new_to_orig_clause.push(orig_index);
        }
    }

    if problem.is_fixedpoint_format() {
        new_problem.set_fixedpoint_format();
    }

    let total_clones: usize = clone_ids.values().map(BTreeMap::len).sum();
    let report = TransformMemoryReport::reversible("pc_split")
        .with_fact("pc_split_predicates", clone_ids.len().to_string())
        .with_fact("pc_split_clones", total_clones.to_string());

    Some((
        new_problem,
        Box::new(PcSplitBackTranslator {
            clone_ids,
            reverse,
            new_to_orig_clause,
            original_sorts,
            input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                .then(|| std::sync::Arc::new(problem.clone())),
            report,
        }),
    ))
}

/// Back-translator for pc-directed location splitting.
struct PcSplitBackTranslator {
    /// orig predicate -> pc value -> clone id (values sorted).
    clone_ids: FxHashMap<PredicateId, BTreeMap<ChcExpr, PredicateId>>,
    /// new predicate -> (orig predicate, Some(pc value) for clones).
    reverse: FxHashMap<PredicateId, (PredicateId, Option<ChcExpr>)>,
    /// transformed clause index -> original clause index.
    new_to_orig_clause: Vec<usize>,
    /// Original argument sorts per original predicate.
    original_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    /// INPUT problem retained for exact ground-derivation reconstruction.
    ///
    /// Pc splitting keeps a 1:1 clause correspondence but removes each split
    /// predicate's pinned pc argument and folds its defining equality out of
    /// the output constraint.  Mapping the recorded clause index back and
    /// completing the richer input clause restores that pc value.  The shared
    /// clause-map translator validates the completed derivation on this input
    /// problem before returning it.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
    report: TransformMemoryReport,
}

impl PcSplitBackTranslator {
    /// Canonical variable list for an original predicate.
    fn canonical_vars(&self, pred: PredicateId) -> Option<Vec<ChcVar>> {
        let sorts = self.original_sorts.get(&pred)?;
        Some(
            sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(canonical_var_name(pred, i), sort.clone()))
                .collect(),
        )
    }

    /// Rename a clone interpretation's parameters onto `target` (the original
    /// predicate's canonical vars, arg0 excluded). Arity mismatch degrades to
    /// `true` (weakest honest interpretation); the original-clause
    /// verification gate decides acceptance.
    fn rename_clone_formula(interp: &PredicateInterpretation, target: &[ChcVar]) -> ChcExpr {
        if interp.vars.len() != target.len() {
            return ChcExpr::Bool(true);
        }
        let subst: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .zip(target.iter())
            .filter(|(from, to)| from != to)
            .map(|(from, to)| (from.clone(), ChcExpr::var(to.clone())))
            .collect();
        interp.formula.substitute(&subst)
    }

    /// Convert a pc literal to the `i64` trace-assignment domain.
    fn pc_value_as_i64(value: &ChcExpr) -> Option<i64> {
        match value {
            ChcExpr::Int(i) => i64::try_from(*i).ok(),
            ChcExpr::BitVec(v, _) => i64::try_from(*v).ok(),
            ChcExpr::Bool(b) => Some(i64::from(*b)),
            _ => None,
        }
    }

    /// Convert a pc literal to an `SmtValue` witness instance.
    fn pc_value_as_smt(value: &ChcExpr) -> Option<SmtValue> {
        match value {
            ChcExpr::Int(i) => Some(SmtValue::Int(*i)),
            ChcExpr::BitVec(v, w) => Some(SmtValue::bitvec_from_u128(*v, *w)),
            ChcExpr::Bool(b) => Some(SmtValue::Bool(*b)),
            _ => None,
        }
    }

    /// Rename a canonical clone-space name `__p{new}_a{i}` into original
    /// space `__p{orig}_a{i+shift}`. Non-canonical names pass through.
    fn rename_canonical_name(
        name: &str,
        new_pred: PredicateId,
        orig_pred: PredicateId,
        shift: usize,
    ) -> String {
        let prefix = format!("__p{}_a", new_pred.index());
        if let Some(rest) = name.strip_prefix(&prefix) {
            if let Ok(arg_idx) = rest.parse::<usize>() {
                return canonical_var_name(orig_pred, arg_idx + shift);
            }
        }
        name.to_string()
    }

    fn map_clause_index(&self, index: usize) -> Option<usize> {
        self.new_to_orig_clause.get(index).copied()
    }
}

impl BackTranslator for PcSplitBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let input_problem = self.input_problem.clone()?;
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::from_index_map(
            "pc-split",
            input_problem,
            &self.new_to_orig_clause,
        )
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "pc-split"
    }

    /// Disjunctive model reassembly: for each split predicate `P` with
    /// values `{v}` and clone interpretations `I_v`,
    /// `P(a0, a...) := \/_v (a0 = v /\ I_v(a...))`. Clones the model omits
    /// contribute `a0 = v` disjuncts with `true` bodies (unconstrained).
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        let mut translated = ValidityWitness::new();

        // Passthrough predicates: keep the interpretation, re-keyed.
        for (new_id, interp) in witness.iter() {
            if let Some((orig_id, None)) = self.reverse.get(new_id) {
                translated.set(*orig_id, interp.clone());
            }
        }

        // Split predicates: disjunctive reassembly over canonical vars.
        for (orig_id, per_value) in &self.clone_ids {
            let Some(vars) = self.canonical_vars(*orig_id) else {
                continue;
            };
            let (pc_var, rest_vars) = match vars.split_first() {
                Some((pc, rest)) => (pc.clone(), rest.to_vec()),
                None => continue,
            };
            let mut disjuncts = Vec::with_capacity(per_value.len());
            for (value, clone_id) in per_value {
                let pinned = ChcExpr::eq(ChcExpr::var(pc_var.clone()), value.clone());
                let body = match witness.get(clone_id) {
                    Some(interp) => Self::rename_clone_formula(interp, &rest_vars),
                    None => ChcExpr::Bool(true),
                };
                disjuncts.push(ChcExpr::and(pinned, body));
            }
            let formula = ChcExpr::or_all(disjuncts);
            translated.set(*orig_id, PredicateInterpretation::new(vars, formula));
        }

        translated
    }

    /// Witness remapping: predicate ids back to originals, clause indices
    /// through the recorded map, canonical vars shifted one position right,
    /// and the pc value re-attached to states/instances/assignments.
    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        let mut translated = witness;

        for step in &mut translated.steps {
            let Some((orig_id, value)) = self.reverse.get(&step.predicate).cloned() else {
                continue;
            };
            let shift = usize::from(value.is_some());
            let new_pred = step.predicate;
            step.predicate = orig_id;
            step.clause_index = step.clause_index.and_then(|i| self.map_clause_index(i));
            if shift > 0 || new_pred != orig_id {
                let assignments = std::mem::take(&mut step.assignments);
                step.assignments = assignments
                    .into_iter()
                    .map(|(name, v)| {
                        (
                            Self::rename_canonical_name(&name, new_pred, orig_id, shift),
                            v,
                        )
                    })
                    .collect();
            }
            if let Some(value) = &value {
                if let Some(pc) = Self::pc_value_as_i64(value) {
                    step.assignments.insert(canonical_var_name(orig_id, 0), pc);
                }
            }
        }

        if let Some(derivation) = &mut translated.witness {
            derivation.query_clause = derivation
                .query_clause
                .and_then(|i| self.map_clause_index(i));
            for entry in &mut derivation.entries {
                let Some((orig_id, value)) = self.reverse.get(&entry.predicate).cloned() else {
                    continue;
                };
                let new_pred = entry.predicate;
                let shift = usize::from(value.is_some());
                entry.predicate = orig_id;
                entry.incoming_clause =
                    entry.incoming_clause.and_then(|i| self.map_clause_index(i));

                let Some(orig_sorts) = self.original_sorts.get(&orig_id) else {
                    continue;
                };
                // Shift canonical state vars from clone space to original
                // space: clone arg i has the sort of original arg i+shift.
                let subst: Vec<(ChcVar, ChcExpr)> = orig_sorts
                    .iter()
                    .enumerate()
                    .skip(shift)
                    .map(|(orig_idx, sort)| {
                        let from = ChcVar::new(
                            canonical_var_name(new_pred, orig_idx - shift),
                            sort.clone(),
                        );
                        let to = ChcVar::new(canonical_var_name(orig_id, orig_idx), sort.clone());
                        (from, ChcExpr::var(to))
                    })
                    .filter(|(from, to)| !matches!(to, ChcExpr::Var(v) if v == from))
                    .collect();
                let mut state = entry.state.substitute(&subst);
                if let (Some(value), Some(pc_sort)) = (&value, orig_sorts.first()) {
                    let pc_var = ChcVar::new(canonical_var_name(orig_id, 0), pc_sort.clone());
                    state = ChcExpr::and(ChcExpr::eq(ChcExpr::var(pc_var), value.clone()), state);
                }
                entry.state = state;

                let instances = std::mem::take(&mut entry.instances);
                entry.instances = instances
                    .into_iter()
                    .map(|(name, v)| {
                        (
                            Self::rename_canonical_name(&name, new_pred, orig_id, shift),
                            v,
                        )
                    })
                    .collect();
                if let Some(value) = &value {
                    if let Some(pc) = Self::pc_value_as_smt(value) {
                        entry.instances.insert(canonical_var_name(orig_id, 0), pc);
                    }
                }
            }
        }

        translated
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.report.clone()
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
