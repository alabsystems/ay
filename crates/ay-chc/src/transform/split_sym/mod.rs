// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SPLIT-SYM: Eldarica-style symbol splitting (CHC-COMP agenda #9).
//!
//! Clones every predicate whose argument at some position is a
//! constraint-implied literal constant in EVERY occurrence (head and body,
//! across all clauses) — the "control-state / program-counter argument"
//! pattern of SSL state machines and control-heavy lustre encodings. One
//! clone is produced per constant value; each clause is specialized to the
//! single clone tuple its pins force, the split argument is dropped, and the
//! constant is substituted into the constraint (folding guards, so clauses
//! whose value combination is contradictory vanish). Reimplements the *idea*
//! of Eldarica's `SymbolSplitter` from scratch; no competitor code copied.
//!
//! # Soundness (G1)
//!
//! The transform is an exact partition of the least model: every derivable
//! fact of `P` carries one of the finitely many head-pinned values at the
//! split position, so `P(xs) <=> OR_v (xs[j] = v /\ P_v(xs \ j))`.
//!
//! * SAT: [`SplitSymBackTranslator::translate_validity`] reassembles the
//!   original predicate's interpretation as exactly that disjunction over the
//!   clone interpretations. The result is certified on the ORIGINAL clauses
//!   by the portfolio firewall (`verify_model_per_rule`), fail-closed.
//! * UNSAT: derivations in the split system map 1:1 onto original
//!   derivations. The back-translator remaps clone predicate ids, canonical
//!   variable names (`__p{clone}_a{k}` -> `__p{orig}_a{k'}` with the split
//!   position re-inserted), witness states/instances (conjoining the split
//!   value), and clause indices ([`ClauseIndexMap`]), then the witness is
//!   replayed on the ORIGINAL clauses (`verified_unsafe_from_witness` /
//!   `verify_counterexample`), fail-closed.
//!
//! # Gating
//!
//! * per-predicate value cap [`MAX_SPLIT_VALUES`] (~64 control states);
//! * per-predicate budget `clauses * values <= MAX_CLAUSE_VALUE_BUDGET`;
//! * global clone cap [`MAX_TOTAL_CLONES`];
//! * a split argument must have at least 2 values (1 value is plain constant
//!   propagation — the condense superpass already covers it).
//!
//! Kill switch: `AY_CHC_DISABLE_SPLIT_SYM=1` disables the pass entirely.

use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
    PredicateInterpretation,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::condense::{ClauseIndexMap, ConstantPropagator};
use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};

/// Per-predicate cap on the number of distinct split values (control states).
/// The ssh-simplified SSL state machines take ~30 values; 64 leaves headroom
/// without risking a clone explosion.
pub(crate) const MAX_SPLIT_VALUES: usize = 64;

/// Global cap on the total number of clone predicates created by one pass.
const MAX_TOTAL_CLONES: usize = 512;

/// Per-predicate budget: `clause_count * |values|` must stay under this bound
/// so specialization work stays proportional to the input size.
const MAX_CLAUSE_VALUE_BUDGET: usize = 1_000_000;

/// Kill switch: `AY_CHC_DISABLE_SPLIT_SYM=1` (or any value other than `0`)
/// disables the symbol splitter. Default: enabled.
pub(crate) fn split_sym_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_SPLIT_SYM")
        .map(|v| v == "0")
        .unwrap_or(true)
}

/// Split-candidate state for one predicate argument position.
#[derive(Clone, Debug)]
struct Candidate {
    /// Distinct literal values seen across occurrences (first-seen order,
    /// deterministic). Capped at [`MAX_SPLIT_VALUES`].
    values: Vec<ChcExpr>,
    /// Every occurrence so far was a literal or constraint-pinned variable.
    splittable: bool,
}

impl Candidate {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            splittable: true,
        }
    }
}

/// One accepted predicate split.
struct SplitSpec {
    orig: PredicateId,
    /// Argument position being split away.
    pos: usize,
    /// Value -> clone id, aligned by index.
    values: Vec<ChcExpr>,
    clones: Vec<PredicateId>,
}

impl SplitSpec {
    fn clone_for_value(&self, value: &ChcExpr) -> Option<PredicateId> {
        self.values
            .iter()
            .position(|v| v == value)
            .map(|i| self.clones[i])
    }
}

/// Eldarica-style symbol splitter (see module docs).
pub(crate) struct SymbolSplitter {
    verbose: bool,
}

impl SymbolSplitter {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Evaluate one predicate-occurrence argument to its pinned literal, if any.
    fn occurrence_value(arg: &ChcExpr, pins: &FxHashMap<String, ChcExpr>) -> Option<ChcExpr> {
        if ConstantPropagator::is_literal(arg) {
            return Some(arg.clone());
        }
        if let ChcExpr::Var(v) = arg {
            return pins.get(&v.name).cloned();
        }
        None
    }

    /// Scan all occurrences of all predicates and return the candidate table.
    /// `vacuous[idx]` marks clauses whose constraint pins conflict (they never
    /// fire and are dropped during specialization).
    fn analyze(problem: &ChcProblem) -> (FxHashMap<(PredicateId, usize), Candidate>, Vec<bool>) {
        let mut candidates: FxHashMap<(PredicateId, usize), Candidate> = FxHashMap::default();
        for pred in problem.predicates() {
            for j in 0..pred.arity() {
                candidates.insert((pred.id, j), Candidate::new());
            }
        }

        let mut vacuous = vec![false; problem.clauses().len()];
        for (idx, clause) in problem.clauses().iter().enumerate() {
            let Some(pins) = ConstantPropagator::constraint_pins(clause) else {
                // Conflicting pins: the clause constraint is unsatisfiable, so
                // the clause imposes nothing on any occurrence.
                vacuous[idx] = true;
                continue;
            };

            let head_occurrence = match &clause.head {
                ClauseHead::Predicate(pid, args) => Some((*pid, args)),
                ClauseHead::False => None,
            };
            let occurrences = clause
                .body
                .predicates
                .iter()
                .map(|(pid, args)| (*pid, args))
                .chain(head_occurrence);

            for (pid, args) in occurrences {
                // Defensive: an occurrence whose argument count disagrees with
                // the declaration disqualifies the predicate entirely (the
                // rewrite phase indexes occurrences by declared position).
                let arity = problem
                    .get_predicate(pid)
                    .map_or(0, crate::Predicate::arity);
                if args.len() != arity {
                    for j in 0..arity.max(args.len()) {
                        if let Some(candidate) = candidates.get_mut(&(pid, j)) {
                            candidate.splittable = false;
                        }
                    }
                    continue;
                }
                for (j, arg) in args.iter().enumerate() {
                    let Some(candidate) = candidates.get_mut(&(pid, j)) else {
                        continue;
                    };
                    if !candidate.splittable {
                        continue;
                    }
                    match Self::occurrence_value(arg, &pins) {
                        Some(value) => {
                            if !candidate.values.contains(&value) {
                                if candidate.values.len() >= MAX_SPLIT_VALUES {
                                    candidate.splittable = false;
                                } else {
                                    candidate.values.push(value);
                                }
                            }
                        }
                        None => candidate.splittable = false,
                    }
                }
            }
        }
        (candidates, vacuous)
    }

    /// Pick at most one split position per predicate (fewest values, then
    /// lowest position) and apply the value/clone/budget gates.
    fn select_splits(
        problem: &ChcProblem,
        candidates: &FxHashMap<(PredicateId, usize), Candidate>,
    ) -> Vec<(PredicateId, usize, Vec<ChcExpr>)> {
        let clause_count = problem.clauses().len();
        let mut per_pred: Vec<(PredicateId, usize, Vec<ChcExpr>)> = Vec::new();
        for pred in problem.predicates() {
            let mut best: Option<(usize, &Candidate)> = None;
            for j in 0..pred.arity() {
                let Some(candidate) = candidates.get(&(pred.id, j)) else {
                    continue;
                };
                // A split needs >= 2 values: a single value is constant
                // propagation (condense covers it), zero means unused.
                if !candidate.splittable || candidate.values.len() < 2 {
                    continue;
                }
                if clause_count.saturating_mul(candidate.values.len()) > MAX_CLAUSE_VALUE_BUDGET {
                    continue;
                }
                let better = match &best {
                    Some((_, current)) => candidate.values.len() < current.values.len(),
                    None => true,
                };
                if better {
                    best = Some((j, candidate));
                }
            }
            if let Some((j, candidate)) = best {
                per_pred.push((pred.id, j, candidate.values.clone()));
            }
        }

        // Global clone budget: keep the cheapest splits first (deterministic:
        // value count, then predicate id).
        per_pred.sort_by_key(|(pid, _, values)| (values.len(), pid.index()));
        let mut total = 0usize;
        per_pred.retain(|(_, _, values)| {
            if total + values.len() > MAX_TOTAL_CLONES {
                return false;
            }
            total += values.len();
            true
        });
        // Restore predicate order for deterministic clone declaration.
        per_pred.sort_by_key(|(pid, _, _)| pid.index());
        per_pred
    }

    /// Fresh clone name that does not collide with any declared predicate.
    fn clone_name(problem: &ChcProblem, base: &str, pos: usize, value_idx: usize) -> String {
        let mut name = format!("{base}__ssym{pos}_{value_idx}");
        while problem.lookup_predicate(&name).is_some() {
            name.push('_');
        }
        name
    }
}

impl Transformer for SymbolSplitter {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if problem.clauses().is_empty() || problem.predicates().is_empty() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        let (candidates, vacuous) = Self::analyze(&problem);
        let splits = Self::select_splits(&problem, &candidates);
        if splits.is_empty() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        // Declare original predicates first (identical ids), clones after.
        let mut new_problem = ChcProblem::new();
        for pred in problem.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        let mut specs: FxHashMap<PredicateId, SplitSpec> = FxHashMap::default();
        for (pid, pos, values) in splits {
            let pred = problem
                .get_predicate(pid)
                .expect("split predicate must exist");
            let clone_sorts: Vec<ChcSort> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .filter_map(|(k, sort)| (k != pos).then(|| sort.clone()))
                .collect();
            let clones: Vec<PredicateId> = (0..values.len())
                .map(|value_idx| {
                    let name = Self::clone_name(&new_problem, &pred.name, pos, value_idx);
                    new_problem.declare_predicate(name, clone_sorts.clone())
                })
                .collect();
            specs.insert(
                pid,
                SplitSpec {
                    orig: pid,
                    pos,
                    values,
                    clones,
                },
            );
        }

        // Specialize clauses: each occurrence of a split predicate names
        // exactly one clone (its pinned value), the split argument is dropped
        // and the constant substituted into the constraint.
        let mut index_map = ClauseIndexMap::new();
        for (idx, clause) in problem.clauses().iter().enumerate() {
            if vacuous[idx] {
                // Conflicting pins: the original clause is vacuously true.
                // Register a folded-false body so `add_clause` prunes it while
                // the index map records the drop (fail-closed replay).
                index_map.record_add(
                    &mut new_problem,
                    HornClause::new(
                        ClauseBody::new(clause.body.predicates.clone(), Some(ChcExpr::Bool(false))),
                        clause.head.clone(),
                    ),
                    idx,
                );
                continue;
            }
            let pins = ConstantPropagator::constraint_pins(clause)
                .expect("non-vacuous clause has consistent pins");

            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            let mut specialize =
                |pid: PredicateId, args: &[ChcExpr]| -> (PredicateId, Vec<ChcExpr>) {
                    let Some(spec) = specs.get(&pid) else {
                        return (pid, args.to_vec());
                    };
                    let value = Self::occurrence_value(&args[spec.pos], &pins)
                        .expect("split occurrence must be pinned");
                    let clone_id = spec
                        .clone_for_value(&value)
                        .expect("occurrence value is in the collected value set");
                    if let ChcExpr::Var(v) = &args[spec.pos] {
                        if !subst.iter().any(|(sv, _)| sv == v) {
                            subst.push((v.clone(), value));
                        }
                    }
                    let new_args: Vec<ChcExpr> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(k, arg)| (k != spec.pos).then(|| arg.clone()))
                        .collect();
                    (clone_id, new_args)
                };

            let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
                .body
                .predicates
                .iter()
                .map(|(pid, args)| specialize(*pid, args))
                .collect();
            let new_head = match &clause.head {
                ClauseHead::Predicate(pid, args) => {
                    let (new_pid, new_args) = specialize(*pid, args);
                    ClauseHead::Predicate(new_pid, new_args)
                }
                ClauseHead::False => ClauseHead::False,
            };

            let constraint = if subst.is_empty() {
                clause.body.constraint.clone()
            } else {
                let mut conjuncts: Vec<ChcExpr> = clause
                    .body
                    .constraint
                    .as_ref()
                    .map(|c| c.substitute(&subst).simplify_constants())
                    .into_iter()
                    .filter(|c| !matches!(c, ChcExpr::Bool(true)))
                    .collect();
                // Keep the pinning equalities: pinned variables may still
                // occur at non-split positions of other predicates, and the
                // pins keep the specialized clause exactly equivalent.
                for (v, c) in &subst {
                    conjuncts.push(ChcExpr::eq(ChcExpr::var(v.clone()), c.clone()));
                }
                Some(ChcExpr::and_all(conjuncts))
            };

            let mut new_clause =
                HornClause::new(ClauseBody::new(new_body_preds, constraint), new_head);
            new_clause.action_id = clause.action_id;
            index_map.record_add(&mut new_problem, new_clause, idx);
        }

        if problem.is_fixedpoint_format() {
            new_problem.set_fixedpoint_format();
        }
        // Restore problem-level metadata lost to the `ChcProblem::new()`
        // rebuild (mirrors the condense superpass): datatype definitions feed
        // DtFlattener/SMT contexts, action names feed TLA+ reports, and the
        // query-evidence bit keeps `ChcProblem::validate` satisfied when every
        // query arm folded away.
        for (name, ctors) in problem.datatype_defs() {
            new_problem.add_datatype_def(name.clone(), ctors.clone());
        }
        for name in problem.action_names() {
            new_problem.declare_action(name.clone());
        }
        if problem.has_query_evidence() && !new_problem.has_query_evidence() {
            new_problem.add_clause(HornClause::new(
                ClauseBody::new(Vec::new(), Some(ChcExpr::Bool(false))),
                ClauseHead::False,
            ));
        }

        if self.verbose {
            safe_eprintln!(
                "CHC split-sym: split {} predicate(s) into {} clone(s); {} clauses -> {}",
                specs.len(),
                specs.values().map(|s| s.clones.len()).sum::<usize>(),
                problem.clauses().len(),
                new_problem.clauses().len()
            );
        }

        let mut original_sorts: FxHashMap<PredicateId, Vec<ChcSort>> = FxHashMap::default();
        for pred in problem.predicates() {
            original_sorts.insert(pred.id, pred.arg_sorts.clone());
        }
        let mut clone_to_orig: FxHashMap<PredicateId, (PredicateId, usize, ChcExpr)> =
            FxHashMap::default();
        for spec in specs.values() {
            for (clone_id, value) in spec.clones.iter().zip(spec.values.iter()) {
                clone_to_orig.insert(*clone_id, (spec.orig, spec.pos, value.clone()));
            }
        }
        let mut split_specs: Vec<SplitSpec> = specs.into_values().collect();
        split_specs.sort_by_key(|spec| spec.orig.index());

        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(SplitSymBackTranslator {
                splits: split_specs,
                clone_to_orig,
                original_sorts,
                index_map,
            }),
        }
    }
}

/// Back-translator for [`SymbolSplitter`] (G1).
struct SplitSymBackTranslator {
    splits: Vec<SplitSpec>,
    /// clone id -> (original id, split position, split value).
    clone_to_orig: FxHashMap<PredicateId, (PredicateId, usize, ChcExpr)>,
    original_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    index_map: ClauseIndexMap,
}

impl SplitSymBackTranslator {
    /// Sort of a split literal value (for the reconstructed witness vars).
    fn literal_sort(value: &ChcExpr) -> Option<ChcSort> {
        match value {
            ChcExpr::Bool(_) => Some(ChcSort::Bool),
            ChcExpr::Int(_) => Some(ChcSort::Int),
            ChcExpr::Real(_, _) => Some(ChcSort::Real),
            ChcExpr::BitVec(_, width) => Some(ChcSort::BitVec(*width)),
            _ => None,
        }
    }

    /// i64 encoding of a split value for `CounterexampleStep::assignments`.
    fn literal_i64(value: &ChcExpr) -> Option<i64> {
        match value {
            ChcExpr::Bool(b) => Some(i64::from(*b)),
            ChcExpr::Int(i) => i64::try_from(*i).ok(),
            ChcExpr::BitVec(v, _) => i64::try_from(*v).ok(),
            _ => None,
        }
    }

    /// `SmtValue` encoding of a split value for witness-entry instances.
    fn literal_smt_value(value: &ChcExpr) -> Option<crate::smt::SmtValue> {
        match value {
            ChcExpr::Bool(b) => Some(crate::smt::SmtValue::Bool(*b)),
            ChcExpr::Int(i) => Some(crate::smt::SmtValue::Int(*i)),
            ChcExpr::BitVec(v, width) => Some(crate::smt::SmtValue::BitVec(*v, *width)),
            _ => None,
        }
    }

    /// Rename a clone-space canonical variable name (`__p{clone}_a{k}`) to
    /// original space, shifting argument indices past the split position.
    fn rename_canonical(&self, name: &str) -> Option<String> {
        let rest = name.strip_prefix("__p")?;
        let (idx_str, arg_str) = rest.split_once("_a")?;
        let idx: u32 = idx_str.parse().ok()?;
        let (orig, pos, _) = self.clone_to_orig.get(&PredicateId::new(idx))?;
        let arg_idx: usize = arg_str.parse().ok()?;
        let shifted = if arg_idx >= *pos {
            arg_idx + 1
        } else {
            arg_idx
        };
        Some(crate::lemma_hints::canonical_var_name(*orig, shifted))
    }
}

impl BackTranslator for SplitSymBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        let mut new_witness = ValidityWitness::new();
        // Pass through interpretations that are neither clones nor the (now
        // unconstrained) original declarations of split predicates.
        let split_origs: Vec<PredicateId> = self.splits.iter().map(|s| s.orig).collect();
        for (pred_id, interp) in witness.iter() {
            if self.clone_to_orig.contains_key(pred_id) || split_origs.contains(pred_id) {
                continue;
            }
            new_witness.set(*pred_id, interp.clone());
        }

        // Reassemble each split predicate as the disjunction over its clones:
        // P(xs) := OR_v (xs[pos] = v /\ M(P_v)(xs \ pos)).
        for spec in &self.splits {
            let Some(sorts) = self.original_sorts.get(&spec.orig) else {
                continue;
            };
            let vars: Vec<ChcVar> = sorts
                .iter()
                .enumerate()
                .map(|(k, sort)| {
                    ChcVar::new(format!("__ssym_p{}_a{k}", spec.orig.index()), sort.clone())
                })
                .collect();
            let reduced: Vec<&ChcVar> = vars
                .iter()
                .enumerate()
                .filter_map(|(k, v)| (k != spec.pos).then_some(v))
                .collect();

            let mut disjuncts: Vec<ChcExpr> = Vec::new();
            for (clone_id, value) in spec.clones.iter().zip(spec.values.iter()) {
                let Some(interp) = witness.get(clone_id) else {
                    // Missing clone interpretation: treat the disjunct as
                    // false. An under-approximate model fails original
                    // verification and the verdict stays fail-closed Unknown.
                    continue;
                };
                if interp.vars.len() != reduced.len() {
                    continue;
                }
                let rename: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .zip(reduced.iter())
                    .filter(|(from, to)| from.name != to.name)
                    .map(|(from, to)| (from.clone(), ChcExpr::var((*to).clone())))
                    .collect();
                let formula = interp.formula.substitute(&rename);
                disjuncts.push(ChcExpr::and_all([
                    ChcExpr::eq(ChcExpr::var(vars[spec.pos].clone()), value.clone()),
                    formula,
                ]));
            }
            new_witness.set(
                spec.orig,
                PredicateInterpretation::new(vars, ChcExpr::or_all(disjuncts)),
            );
        }
        new_witness
    }

    fn translate_invalidity(&self, mut witness: InvalidityWitness) -> InvalidityWitness {
        for step in &mut witness.steps {
            let Some((orig, pos, value)) = self.clone_to_orig.get(&step.predicate).cloned() else {
                continue;
            };
            step.predicate = orig;
            let assignments = std::mem::take(&mut step.assignments);
            step.assignments = assignments
                .into_iter()
                .map(|(name, v)| (self.rename_canonical(&name).unwrap_or(name), v))
                .collect();
            if let Some(v) = Self::literal_i64(&value) {
                step.assignments
                    .entry(crate::lemma_hints::canonical_var_name(orig, pos))
                    .or_insert(v);
            }
        }

        if let Some(derivation) = &mut witness.witness {
            for entry in &mut derivation.entries {
                let Some((orig, pos, value)) = self.clone_to_orig.get(&entry.predicate).cloned()
                else {
                    continue;
                };
                entry.predicate = orig;

                let instances = std::mem::take(&mut entry.instances);
                entry.instances = instances
                    .into_iter()
                    .map(|(name, v)| (self.rename_canonical(&name).unwrap_or(name), v))
                    .collect();
                if let Some(v) = Self::literal_smt_value(&value) {
                    entry
                        .instances
                        .entry(crate::lemma_hints::canonical_var_name(orig, pos))
                        .or_insert(v);
                }

                let state_subst: Vec<(ChcVar, ChcExpr)> = entry
                    .state
                    .vars()
                    .into_iter()
                    .filter_map(|var| {
                        let renamed = self.rename_canonical(&var.name)?;
                        let new_var = ChcVar::new(renamed, var.sort.clone());
                        Some((var, ChcExpr::Var(new_var)))
                    })
                    .collect();
                if !state_subst.is_empty() {
                    entry.state = entry.state.substitute(&state_subst);
                }
                if let Some(sort) = Self::literal_sort(&value) {
                    let split_var =
                        ChcVar::new(crate::lemma_hints::canonical_var_name(orig, pos), sort);
                    entry.state = ChcExpr::and_all([
                        entry.state.clone(),
                        ChcExpr::eq(ChcExpr::var(split_var), value.clone()),
                    ]);
                }
            }
        }

        self.index_map.translate_invalidity(witness)
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "split_sym",
            [
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
        .with_fact("split_predicates", format!("{}", self.splits.len()))
        .with_fact(
            "split_clones",
            format!(
                "{}",
                self.splits.iter().map(|s| s.clones.len()).sum::<usize>()
            ),
        )
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
