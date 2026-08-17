// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing pipeline for CHC portfolio solving.
//!
//! Builds a [`PreprocessSummary`] capturing the transformed problem and metadata
//! needed by the adaptive routing layer and portfolio engine dispatch.

use crate::transform::condense::UnreachableClauseEliminator;
use crate::transform::{
    condense_enabled, split_sym_enabled, ArrayStoreForwarder, BackTranslator, BvToBoolBitBlaster,
    BvToIntAbstractor, ClauseInliner, CompositeBackTranslator, CondenseSuperpass,
    DeadParamEliminator, DtFlattener, GroundTableReadConcretizer, IdentityBackTranslator,
    IntervalPropagator, InvalidityWitness, LocalVarEliminator, MultiEdgeMerger, NodeEliminator,
    PcSplitter, SymbolSplitter, TransformMemoryReport, TransformationPipeline,
    TransformationResult, ValidityWitness,
};
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseHead};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// Rank-6 graph collapse (golem-style MultiEdgeMerger + NodeEliminator).
/// DEFAULT ON (`AY_GRAPH_COLLAPSE=0` disables). Flipped after the gate
/// battery: 120-sample LIA-Lin 60->64/120 with 0 wrong; non-vmt gap subset
/// 2/17->6/17 @60s and 7/17 @300s; prior-form regression canaries
/// (s_split_36/13) hold; trivial-Unsafe and Step-4.20 acceptance paths are
/// fail-closed on non-identity transform stacks (is_identity_grade), so every
/// Safe/Unsafe answer still validates against the ORIGINAL clauses.
fn graph_collapse_enabled() -> bool {
    // B27: CLI-owned; env retired.
    crate::ab_switches::get().graph_collapse
}

pub(crate) fn sort_contains_recursive_bv(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::BitVec(_) => true,
        ChcSort::Array(key, value) => {
            sort_contains_recursive_bv(key.as_ref()) || sort_contains_recursive_bv(value.as_ref())
        }
        ChcSort::Datatype { constructors, .. } => constructors.iter().any(|ctor| {
            ctor.selectors
                .iter()
                .any(|sel| sort_contains_recursive_bv(&sel.sort))
        }),
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::Uninterpreted(_) => false,
    }
}

pub(crate) fn problem_contains_recursive_bv_sorts(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(sort_contains_recursive_bv)
}

/// FIX #2b: once-per-solve sharing of the pc-split+condense stage.
///
/// Measured: the same original problem runs the full pc-split+condense
/// fixpoint up to three times per solve — Lane B (`build_int_only`), Lane C
/// (`build_bv_native`) and the final portfolio (`build` via
/// `enable_preprocessing`) each start from `condense_stage(problem.clone())`.
/// On SLayerCF copy/destroy and ssh that stage is the dominant preprocessing
/// cost, so the re-runs alone were a ~2/3-wasted budget window.
///
/// The cache is process-wide and strictly exact: entries are matched by a
/// cheap fingerprint FIRST and then verified with FULL structural equality
/// against the stored original problem (clones share interned `Arc` children,
/// so the equality walk is near-O(shallow) via the `Arc::ptr_eq` fast path).
/// A hit therefore returns byte-for-byte what a recompute would return (the
/// stage is deterministic given the same env flags, which are part of the
/// entry), so verdicts cannot change; there is no approximate matching.
///
/// Kill switch: `AY_CHC_CONDENSE_SHARE=0` disables sharing entirely.
struct CondenseShareEntry {
    fingerprint: u64,
    /// Env flags the stage output depends on; compared exactly on lookup so
    /// tests toggling kill switches / budgets never see stale entries.
    env_key: String,
    original: ChcProblem,
    condensed: ChcProblem,
    translator: Arc<Mutex<Box<dyn BackTranslator>>>,
}

/// Bounded FIFO: enough for the handful of problems solved concurrently by
/// parallel tests while keeping retained memory trivial.
const CONDENSE_SHARE_CAP: usize = 8;

static CONDENSE_SHARE: OnceLock<Mutex<Vec<CondenseShareEntry>>> = OnceLock::new();
/// Test observability: number of cache hits since process start.
static CONDENSE_SHARE_HITS: AtomicUsize = AtomicUsize::new(0);

// Test hook from the CONDENSE-BOX work (ef7757ec) whose tests were never
// written; the counter is still incremented. Kept for owner review.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) fn condense_share_hits() -> usize {
    CONDENSE_SHARE_HITS.load(Ordering::Relaxed)
}

fn condense_share_enabled() -> bool {
    // B24: the kill-switch env is retired; sharing stays on.
    true
}

/// Every env flag that changes the pc-split+condense output. Stored in the
/// entry and compared exactly on lookup.
fn condense_share_env_key() -> String {
    // B8 dropped the condense budget names; B27 drops SPLIT_SYM / PC_SPLIT /
    // ARRAY_STORE_FORWARDING / GROUND_TABLE_CONCRETIZATION; B54 moves the
    // condense kill onto the set-once carrier too. The one residual variance
    // source is the cfg(test) override, which the key must reflect.
    if crate::ab_switches::get().condense {
        String::new()
    } else {
        "condense-off".to_string()
    }
}

/// Cheap pre-filter fingerprint. Deliberately shallow (counts, names,
/// arities): the authoritative check is `problems_structurally_equal`.
fn condense_share_fingerprint(problem: &ChcProblem) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    problem.predicates().len().hash(&mut h);
    for pred in problem.predicates() {
        pred.name.hash(&mut h);
        pred.arg_sorts.hash(&mut h);
    }
    problem.clauses().len().hash(&mut h);
    for clause in problem.clauses() {
        for (pid, args) in &clause.body.predicates {
            pid.hash(&mut h);
            args.len().hash(&mut h);
        }
        clause.body.constraint.is_some().hash(&mut h);
        match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                1u8.hash(&mut h);
                pid.hash(&mut h);
                args.len().hash(&mut h);
            }
            ClauseHead::False => 0u8.hash(&mut h),
            // `ClauseHead` is non_exhaustive: unknown future variants hash
            // conservatively (still disambiguated by the equality check).
            #[allow(unreachable_patterns)]
            _ => 2u8.hash(&mut h),
        }
        clause.action_id.hash(&mut h);
    }
    problem.is_fixedpoint_format().hash(&mut h);
    h.finish()
}

/// Full structural equality between two problems (authoritative cache check).
/// `ChcExpr::eq` short-circuits on shared `Arc` children, so comparing clones
/// of one problem never walks constraint trees.
fn problems_structurally_equal(a: &ChcProblem, b: &ChcProblem) -> bool {
    a.predicates().len() == b.predicates().len()
        && a.clauses().len() == b.clauses().len()
        && a.is_fixedpoint_format() == b.is_fixedpoint_format()
        && a.has_query_evidence() == b.has_query_evidence()
        && a.action_names() == b.action_names()
        && a.datatype_defs() == b.datatype_defs()
        && a.predicates()
            .iter()
            .zip(b.predicates())
            .all(|(p, q)| p.name == q.name && p.arg_sorts == q.arg_sorts)
        && a.clauses().iter().zip(b.clauses()).all(|(c, d)| {
            c.action_id == d.action_id
                && c.body.predicates == d.body.predicates
                && c.body.constraint == d.body.constraint
                && match (&c.head, &d.head) {
                    (ClauseHead::False, ClauseHead::False) => true,
                    (ClauseHead::Predicate(pi, pa), ClauseHead::Predicate(qi, qa)) => {
                        pi == qi && pa == qa
                    }
                    _ => false,
                }
        })
}

/// Back-translator wrapper sharing one condense-stage translator across the
/// preprocessing pipelines of a single solve. All trait methods take `&self`
/// and the wrapped translators are logically read-only; the mutex only
/// serializes concurrent lane access (poisoning is recovered because a
/// panicked reader cannot leave partial state behind).
struct SharedCondenseBackTranslator(Arc<Mutex<Box<dyn BackTranslator>>>);

impl SharedCondenseBackTranslator {
    fn inner(&self) -> std::sync::MutexGuard<'_, Box<dyn BackTranslator>> {
        self.0
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

impl BackTranslator for SharedCondenseBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        self.inner().translate_validity(witness)
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        self.inner().translate_invalidity(witness)
    }

    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        self.inner().translate_ground_derivation(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        self.inner().ground_translation_name()
    }

    fn had_bitwise_uf_fallback(&self) -> bool {
        self.inner().had_bitwise_uf_fallback()
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.inner().transform_memory()
    }

    fn array_refinement_indices(&self) -> Vec<(ChcSort, ChcExpr)> {
        self.inner().array_refinement_indices()
    }
}

/// Stage -1 of every `build*` pipeline: the unified fixpoint condense
/// superpass (item #4 CONDENSE). Runs on the ORIGINAL problem so predicate
/// chains collapse before BV bit-blasting / int abstraction. Disabled via
/// `--chc-no-condense`; no-ops (identity back-translator) on
/// problems it cannot shrink.
///
/// FIX #2b: results are shared per original problem (see
/// [`CondenseShareEntry`]) so Lane B / Lane C / the final portfolio no longer
/// re-run the fixpoint on the same clauses.
fn condense_stage(problem: ChcProblem, verbose: bool) -> TransformationResult {
    if !condense_share_enabled() {
        return condense_stage_uncached(problem, verbose);
    }

    let fingerprint = condense_share_fingerprint(&problem);
    let env_key = condense_share_env_key();
    let cache = CONDENSE_SHARE.get_or_init(|| Mutex::new(Vec::new()));
    {
        let entries = cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(entry) = entries.iter().find(|e| {
            e.fingerprint == fingerprint
                && e.env_key == env_key
                && problems_structurally_equal(&e.original, &problem)
        }) {
            CONDENSE_SHARE_HITS.fetch_add(1, Ordering::Relaxed);
            if verbose {
                safe_eprintln!(
                    "Portfolio: pc-split+condense stage shared across pipelines (cache hit)"
                );
            }
            return TransformationResult {
                problem: entry.condensed.clone(),
                back_translator: Box::new(SharedCondenseBackTranslator(entry.translator.clone())),
            };
        }
    }

    let result = condense_stage_uncached(problem.clone(), verbose);
    let translator = Arc::new(Mutex::new(result.back_translator));
    {
        let mut entries = cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if entries.len() >= CONDENSE_SHARE_CAP {
            entries.remove(0);
        }
        entries.push(CondenseShareEntry {
            fingerprint,
            env_key,
            original: problem,
            condensed: result.problem.clone(),
            translator: translator.clone(),
        });
    }
    TransformationResult {
        problem: result.problem,
        back_translator: Box::new(SharedCondenseBackTranslator(translator)),
    }
}

fn condense_stage_uncached(problem: ChcProblem, verbose: bool) -> TransformationResult {
    let condense = condense_enabled();
    // SPLIT-SYM (item #9) runs right after the condense fixpoint: condense
    // folds/pins constants first, then the symbol splitter clones predicates
    // whose argument is a constraint-implied constant in every occurrence
    // (control-state args). It gates itself (value cap, clause*value budget)
    // and no-ops (identity back-translator) when no split argument exists.
    let split_sym = split_sym_enabled();
    let mut pipeline = TransformationPipeline::new();
    // PC-SPLIT (SLayerCF pc-directed location splitting, campaign recon
    // lever 8) runs FIRST: it is a strict-shape detector on the ORIGINAL
    // clauses (every occurrence of a predicate must pin arg0 to a constant —
    // program-counter towers), and condense would reshape the towers before
    // it could fire. It self-gates (no-op off-shape) and carries its own
    // kill switch `AY_CHC_DISABLE_PC_SPLIT=1`. Fail-closed: the split forces
    // original-clause validation for Safe and exact witness remapping for
    // Unsafe.
    pipeline = pipeline.with(PcSplitter::new().with_verbose(verbose));
    if condense {
        let mut condense = CondenseSuperpass::new().with_verbose(verbose);
        // Mirror `portfolio_clause_inliner`: only pure-Int problems need the
        // query-body predicates preserved for Unsafe witness reconstruction.
        if !(problem.has_bv_sorts()
            || problem.has_array_sorts()
            || problem.has_real_sorts()
            || problem.has_datatype_sorts())
        {
            condense = condense.preserve_query_body_predicates();
        }
        pipeline = pipeline.with(condense);
    }
    if split_sym {
        pipeline = pipeline.with(SymbolSplitter::new().with_verbose(verbose));
    }
    pipeline.transform(problem)
}

/// Bounded-cost guard for the trailing `DeadParamEliminator` on the large
/// BV+array DAG class (item 4a). The slicer's per-fixpoint-iteration cost is
/// dominated by the per-clause `positions²` flow-edge scan, so bound the sum
/// of squared per-clause argument-position counts (plus a clause-count cap).
fn dead_param_cost_bounded(problem: &ChcProblem) -> bool {
    const MAX_CLAUSES: usize = 16_384;
    const MAX_POSITION_PAIRS: u64 = 1 << 29;
    if problem.clauses().len() > MAX_CLAUSES {
        return false;
    }
    let mut total: u64 = 0;
    for clause in problem.clauses() {
        let mut positions = 0usize;
        for (_, args) in &clause.body.predicates {
            positions += args.len();
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            positions += args.len();
        }
        let p = positions as u64;
        total = total.saturating_add(p.saturating_mul(p));
        if total > MAX_POSITION_PAIRS {
            return false;
        }
    }
    true
}

pub(crate) fn portfolio_clause_inliner(problem: &ChcProblem, verbose: bool) -> ClauseInliner {
    let inliner = ClauseInliner::new().with_verbose(verbose);
    if problem.has_bv_sorts()
        || problem.has_array_sorts()
        || problem.has_real_sorts()
        || problem.has_datatype_sorts()
    {
        inliner
    } else {
        inliner.preserve_query_body_predicates()
    }
}

/// Summary of preprocessing results for reuse between adaptive routing and solving.
///
/// After BvToBool/BvToInt/ClauseInliner/etc., this captures the transformed
/// problem plus metadata needed to route to the correct engine portfolio.
/// Part of #5877: avoids re-running preprocessing when the adaptive layer
/// needs post-preprocess classification.
pub(crate) struct PreprocessSummary {
    pub(crate) original_problem: ChcProblem,
    pub(crate) transformed_problem: ChcProblem,
    pub(crate) back_translator: Box<dyn BackTranslator>,
    pub(crate) bv_abstracted: bool,
    pub(crate) transform_memory: TransformMemoryReport,
}

impl PreprocessSummary {
    fn from_parts(
        original_problem: ChcProblem,
        transformed_problem: ChcProblem,
        back_translator: Box<dyn BackTranslator>,
        bv_abstracted: bool,
    ) -> Self {
        let transform_memory = back_translator.transform_memory();
        Self {
            original_problem,
            transformed_problem,
            back_translator,
            bv_abstracted,
            transform_memory,
        }
    }

    /// Run the standard preprocessing pipeline and compute metadata.
    pub(crate) fn build(problem: ChcProblem, verbose: bool) -> Self {
        Self::build_with_graph_collapse(problem, verbose, graph_collapse_enabled())
    }

    /// [`build`](Self::build) with the graph-collapse stage made explicit so
    /// tests can exercise both paths without mutating process environment.
    pub(crate) fn build_with_graph_collapse(
        problem: ChcProblem,
        verbose: bool,
        graph_collapse: bool,
    ) -> Self {
        // Stage -1: fixpoint condense superpass on the ORIGINAL problem
        // (--chc-no-condense disables). Collapses predicate chains
        // before bit-blasting multiplies argument counts.
        let condense_result = condense_stage(problem.clone(), verbose);

        // Stage 0: forward array store chains (item 4a; cheap no-op without
        // stores, and covers problems the condense clause-count cap skipped),
        // concretize read-only ground-pin table arrays (item 4 Stage 1), then
        // remove dead params BEFORE bit-blasting (saves 8× per dead BV(8))
        let pre_pipeline = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .with(GroundTableReadConcretizer::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(condense_result.problem);

        // Stage 0.5: Flatten DT-sorted predicate args to scalars (#8288).
        // Must run before BvToBool/BvToInt so DT fields containing BV sorts
        // become top-level BV args eligible for bit-blasting.
        let dt_pipeline =
            TransformationPipeline::new().with(DtFlattener::new().with_verbose(verbose));
        let dt_result = dt_pipeline.transform(pre_result.problem);

        // Stage 1: BvToBool (exact bit-blasting) on pre-cleaned problem
        let bvtobool_pipeline =
            TransformationPipeline::new().with(BvToBoolBitBlaster::new().with_verbose(verbose));
        let bvtobool_result = bvtobool_pipeline.transform(dt_result.problem);

        // BvToBool is exact: if it eliminated all BV sorts, the problem is
        // faithfully represented in Bool domain. BvToInt (stage 2) only
        // handles BV sorts that survived BvToBool (width > 64 or Array
        // sub-sorts). Only BvToInt introduces an over-approximation.
        let bv_remains_after_bitblast =
            problem_contains_recursive_bv_sorts(&bvtobool_result.problem);

        // Stage 2: BvToInt + cleanup (may over-approximate remaining BV sorts)
        let cleanup_pipeline = TransformationPipeline::new()
            .with(BvToIntAbstractor::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(portfolio_clause_inliner(&problem, verbose));
        // Note: BvToInt-only path (skipping BvToBool) was tested (#5877) but
        // regresses BV score from 17/205 to ~1/205 — the ITE-heavy modular
        // arithmetic encoding from BvToInt overwhelms LIA engines. Recovering
        // harder BV benchmarks (nested4, simple) requires native BV theory in
        // PDR (like Z3 Spacer) rather than a routing change.
        let result = cleanup_pipeline.transform(bvtobool_result.problem);

        // (#7048) Mod/div expansion is done per-engine (PDR) rather than at portfolio
        // level, because Euclidean axioms add fresh variables that can hurt PDKind/TPA
        // convergence on benchmarks like const_mod_3, dillig22_m, s_multipl_17.

        // Stage 3 (opt-in, AY_GRAPH_COLLAPSE=1): golem-style graph collapse for
        // multi-predicate linear CHC — parallel-edge merging + internal-vertex
        // contraction, then substitution cleanup of the composed constraints.
        // Safe answers still re-validate against the ORIGINAL clauses and
        // Unsafe witnesses replay there (or fail closed to Unknown); see
        // transform/node_eliminator.rs.
        let (transformed_problem, collapse_back_translator) = if graph_collapse {
            let collapse_pipeline = TransformationPipeline::new()
                .with(MultiEdgeMerger::new())
                .with(NodeEliminator::new().with_verbose(verbose))
                .with(LocalVarEliminator::new().with_verbose(verbose))
                .with(DeadParamEliminator::new().with_verbose(verbose));
            let collapse_result = collapse_pipeline.transform(result.problem);
            (
                collapse_result.problem,
                Some(collapse_result.back_translator),
            )
        } else {
            (result.problem, None)
        };

        // Symbol splitting runs after the condense fixpoint, and later
        // inlining/graph collapse can leave a split clone in a query body with
        // no defining head. Re-run exact syntactic reachability at the very
        // end so those newly exposed unreachable query arms become queryless.
        let reachability_result = TransformationPipeline::new()
            .with(UnreachableClauseEliminator::new().with_verbose(verbose))
            .transform(transformed_problem);
        let transformed_problem = reachability_result.problem;

        // Compose back-translators in reverse transform order: final
        // reachability first, graph collapse (when enabled), then cleanup,
        // bvtobool, dt-flatten, pre-elim, and condense.
        let mut inner: Vec<Box<dyn BackTranslator>> = vec![reachability_result.back_translator];
        if let Some(collapse_bt) = collapse_back_translator {
            inner.push(collapse_bt);
        }
        inner.extend([
            result.back_translator,
            bvtobool_result.back_translator,
            dt_result.back_translator,
            pre_result.back_translator,
            condense_result.back_translator,
        ]);
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator { inner });

        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = transformed_problem.clauses().len();
            let orig_preds = problem.predicates().len();
            let new_preds = transformed_problem.predicates().len();
            safe_eprintln!(
                "Portfolio: Preprocessing reduced {} clauses -> {}, {} predicates -> {}",
                orig_clauses,
                new_clauses,
                orig_preds,
                new_preds
            );
        }
        // Only set bv_abstracted if BvToInt had to handle BV sorts that
        // BvToBool couldn't (exact) bit-blast. BvToBool is exact, so if it
        // handled everything, no over-approximation is in effect.
        let bv_abstracted = bv_remains_after_bitblast;
        // Detect pure-Boolean state: all predicate args are Bool or Int after
        // preprocessing. This is the signature of a successfully bit-blasted BV
        // problem that should skip interpolation-heavy engines (#5877).
        let pure_boolean_after_preprocess = transformed_problem.predicates().iter().all(|p| {
            p.arg_sorts
                .iter()
                .all(|s| matches!(s, ChcSort::Bool | ChcSort::Int))
        });
        if verbose {
            if bv_abstracted {
                safe_eprintln!(
                    "Portfolio: Original problem contains recursive BV sorts — Unsafe results require original-domain confirmation"
                );
            }
            if pure_boolean_after_preprocess {
                safe_eprintln!(
                    "Portfolio: Post-preprocess problem is pure Boolean+Int — Boolean lane eligible"
                );
            }
        }
        Self::from_parts(problem, transformed_problem, back_translator, bv_abstracted)
    }

    /// Whether the BvToInt transform used UF fallback for any variable-variable
    /// bitwise operation. When true, re-running with a higher decompose limit
    /// (via `build_int_refined`) could improve precision (#8289).
    pub(crate) fn had_bitwise_uf_fallback(&self) -> bool {
        self.transform_memory
            .has_obligation("bitwise-uf-refinement")
            || self.back_translator.had_bitwise_uf_fallback()
    }

    /// Build a BvToInt-only preprocessing pipeline (no BvToBool bit-blasting).
    ///
    /// Converts BV predicates to integer arithmetic, preserving the original
    /// variable count (no state-space explosion). Used as a parallel lane
    /// alongside BvToBool: BvToInt produces compact LIA problems solvable by
    /// TPA/PDR/PDKIND, while BvToBool works for problems needing bit-level
    /// reasoning (#5877).
    pub(crate) fn build_int_only(problem: ChcProblem, verbose: bool) -> Self {
        // Stage -1: fixpoint condense superpass (--chc-no-condense disables)
        let condense_result = condense_stage(problem.clone(), verbose);

        // Stage 0: forward array store chains (item 4a), concretize read-only
        // ground-pin table arrays (item 4 Stage 1), then remove dead params
        // BEFORE BvToInt (reduces arity before conversion)
        let pre_pipeline = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .with(GroundTableReadConcretizer::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(condense_result.problem);

        // Stage 0.5: Flatten DT-sorted predicate args (#8288)
        let dt_pipeline =
            TransformationPipeline::new().with(DtFlattener::new().with_verbose(verbose));
        let dt_result = dt_pipeline.transform(pre_result.problem);

        // Use exact BvToInt here so Safe results remain sound in the original
        // BV domain. The relaxed encoding is unsound under signed overflow
        // (#6848) and must stay test-only.
        //
        // WORD-BV (#8): IntervalPropagator runs right after BvToInt to
        // discharge `mod 2^w` wraparound casts whose bounds are SMT-proven
        // (fail-closed; kill-switch AY_CHC_DISABLE_WORD_BV).
        let pipeline = TransformationPipeline::new()
            .with(BvToIntAbstractor::new().with_verbose(verbose))
            .with(IntervalPropagator::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(portfolio_clause_inliner(&problem, verbose));
        let result = pipeline.transform(dt_result.problem);
        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = result.problem.clauses().len();
            safe_eprintln!(
                "Portfolio: BvToInt-only preprocessing: {} clauses -> {}",
                orig_clauses,
                new_clauses
            );
        }
        let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
        // Compose back-translators: pipeline (inner) then dt-flatten then
        // pre-elim then condense (outermost)
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![
                result.back_translator,
                dt_result.back_translator,
                pre_result.back_translator,
                condense_result.back_translator,
            ],
        });
        Self::from_parts(problem, result.problem, back_translator, bv_abstracted)
    }

    /// Build a relaxed BvToInt preprocessing pipeline (no modular wrapping).
    ///
    /// Maps BV arithmetic to unbounded integer arithmetic, producing simpler LIA
    /// constraints without the mod/div overhead of exact BvToInt. This enables
    /// faster invariant discovery for BV64 problems where overflow is uncommon
    /// (#4198).
    ///
    /// **Soundness**: relaxed BvToInt is UNSOUND under signed overflow (#6848).
    /// Callers MUST validate Safe results against the original BV problem before
    /// accepting them. Invalid invariants (where overflow matters) will fail
    /// validation and fall through to the exact path.
    pub(crate) fn build_int_relaxed(problem: ChcProblem, verbose: bool) -> Self {
        // Stage -1: fixpoint condense superpass (--chc-no-condense disables)
        let condense_result = condense_stage(problem.clone(), verbose);

        // Stage 0 (+ item 4a array store forwarding, cheap no-op without stores)
        let pre_pipeline = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(condense_result.problem);

        // Stage 0.5: Flatten DT-sorted predicate args (#8288)
        let dt_pipeline =
            TransformationPipeline::new().with(DtFlattener::new().with_verbose(verbose));
        let dt_result = dt_pipeline.transform(pre_result.problem);

        let pipeline = TransformationPipeline::new()
            .with(
                BvToIntAbstractor::new()
                    .with_verbose(verbose)
                    .with_relaxed(true),
            )
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(portfolio_clause_inliner(&problem, verbose));
        let result = pipeline.transform(dt_result.problem);
        if verbose {
            safe_eprintln!(
                "Portfolio: BvToInt-relaxed preprocessing: {} clauses -> {}",
                problem.clauses().len(),
                result.problem.clauses().len()
            );
        }
        let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![
                result.back_translator,
                dt_result.back_translator,
                pre_result.back_translator,
                condense_result.back_translator,
            ],
        });
        Self::from_parts(problem, result.problem, back_translator, bv_abstracted)
    }

    /// Build a BV-native preprocessing pipeline (no BV transforms at all).
    ///
    /// Preserves the original BV sorts and operations, applying only non-BV
    /// transforms (local var elimination, dead param elimination, clause
    /// inlining). The resulting problem retains BV-sorted predicate arguments,
    /// allowing PDR to operate on BV expressions natively via the SMT solver's
    /// BV theory. This matches Z3 Spacer's default behavior where
    /// `xform.bit_blast = false` (#5877 Wave 3).
    ///
    /// Key difference from `build_int_only`: `bv_abstracted` is set to `false`
    /// because the problem is NOT abstracted — BV sorts are preserved. Unsafe
    /// results do not require confirmation against the original problem since
    /// the solver operates in the original domain.
    pub(crate) fn build_bv_native(problem: ChcProblem, verbose: bool) -> Self {
        // #5877: For BV-native single-predicate problems with large transition
        // relations (e.g., bist_cell has 10000 nodes), the preprocessing
        // transforms (LocalVarEliminator, DeadParamEliminator, ClauseInliner)
        // can be extremely slow — each transform walks and potentially rebuilds
        // the entire expression tree. Skip preprocessing for simple BV-native
        // problems (1 predicate, few clauses) where inlining provides no benefit.
        let is_simple = problem.predicates().len() == 1
            && problem.clauses().len() <= 5
            && problem.has_bv_sorts();
        if is_simple {
            if verbose {
                safe_eprintln!(
                    "Portfolio: BV-native skipping preprocessing (simple problem, {} clauses)",
                    problem.clauses().len()
                );
            }
            return Self::from_parts(
                problem.clone(),
                problem,
                Box::new(IdentityBackTranslator),
                false,
            );
        }

        let is_large_bv_array_dag = problem.predicates().len() > 128
            && problem.clauses().len() > 1024
            && problem.has_bv_sorts()
            && problem.has_array_sorts();
        if is_large_bv_array_dag {
            if verbose {
                safe_eprintln!(
                    "Portfolio: BV-native preserving large BV+array predicate DAG ({} predicates, {} clauses)",
                    problem.predicates().len(),
                    problem.clauses().len()
                );
            }
            // Item 4a (model-checker-consumer parity, heavy-memory "235-relation" class):
            // this skip branch is exactly the threaded-memory shape the
            // clause-local store-forwarding pass targets. The slow general
            // passes (LocalVarEliminator/ClauseInliner, #5877) stay skipped;
            // only the bounded-cost forwarding pass runs, plus ONE trailing
            // DeadParamEliminator (arity slicing) when forwarding actually
            // changed something and the slicer's cost bound holds.
            return Self::build_array_forwarding_only(problem, verbose);
        }

        let _t_total = ay_core::time::Instant::now();

        // Stage -1: fixpoint condense superpass (--chc-no-condense disables)
        let condense_result = condense_stage(problem.clone(), verbose);

        // Stage 0.5: Flatten DT-sorted predicate args (#8288)
        let dt_pipeline =
            TransformationPipeline::new().with(DtFlattener::new().with_verbose(verbose));
        let dt_result = dt_pipeline.transform(condense_result.problem);

        let pipeline = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(portfolio_clause_inliner(&problem, verbose));
        let result = pipeline.transform(dt_result.problem);
        if verbose {
            let orig_clauses = problem.clauses().len();
            let new_clauses = result.problem.clauses().len();
            safe_eprintln!(
                "Portfolio: BV-native preprocessing (no BV transforms): {} clauses -> {} ({:?})",
                orig_clauses,
                new_clauses,
                _t_total.elapsed()
            );
        }
        // bv_abstracted is false: the problem retains original BV sorts.
        // Unsafe results are already in the original domain — no confirmation
        // against the original problem is needed.
        Self::from_parts(
            problem,
            result.problem,
            Box::new(CompositeBackTranslator {
                inner: vec![
                    result.back_translator,
                    dt_result.back_translator,
                    condense_result.back_translator,
                ],
            }),
            false,
        )
    }

    /// Bounded-cost forwarding-only preprocessing (item 4, heavy-memory
    /// "235-relation" class): the clause-local [`ArrayStoreForwarder`] plus
    /// ONE trailing cost-bounded [`DeadParamEliminator`] (arity slicing). The
    /// slicer also runs when forwarding was a no-op — select-only
    /// threaded-memory encodings carry dead memory params without a single
    /// store. No other pass runs — this is the cheap combination safe to
    /// place ahead of the raw acyclic BMC lanes (`solve_bmc_only`, the direct
    /// acyclic probe) which historically ran on the completely unpreprocessed
    /// problem.
    ///
    /// Identity fast paths: problems without array sorts, the
    /// `AY_CHC_DISABLE_ARRAY_STORE_FORWARDING` kill switch (handled inside
    /// the pass), and no-op forwarding all return an identity-grade summary.
    ///
    /// `bv_abstracted` is `false`: sorts are untouched. The transform stack
    /// still reports original-validation obligations, so Safe answers
    /// validate and Unsafe witnesses replay against the ORIGINAL clauses
    /// fail-closed (`transform_memory.is_identity_grade()` is `false` for any
    /// real rewrite).
    pub(crate) fn build_array_forwarding_only(problem: ChcProblem, verbose: bool) -> Self {
        // The kill switch disables the WHOLE lane (forwarder AND trailing
        // slicer), restoring the raw-problem behavior of the acyclic lanes.
        if !problem.has_array_sorts() || !crate::transform::array_store_forwarding_enabled() {
            return Self::from_parts(
                problem.clone(),
                problem,
                Box::new(IdentityBackTranslator),
                false,
            );
        }

        let t_start = ay_core::time::Instant::now();
        let forward_result = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .transform(problem.clone());
        let forwarding_changed = !forward_result.transform_memory().is_identity_grade();
        // Item 4 Stage 1: concretize read-only ground-pin table arrays right
        // after forwarding so the trailing slicer can drop the (now dead)
        // table argument positions. Global-analysis pass: any check failure
        // yields an identity-grade result.
        let conc_result = TransformationPipeline::new()
            .with(GroundTableReadConcretizer::new().with_verbose(verbose))
            .transform(forward_result.problem);
        let concretization_changed = !conc_result.transform_memory().is_identity_grade();
        // Item 4 Stage 4 wiring: flatten DT-sorted predicate args AFTER the
        // concretizer and BEFORE the arity slicer. The model-checker-consumer coroutine
        // encodings carry deep SINGLE-constructor struct towers (variants
        // encoded as parallel fields + a case discriminant), which the
        // flattener already supports; flattening exposes the per-field
        // scalars so the trailing DeadParamEliminator can slice dead columns
        // and the scalar acyclic lanes apply. Self-gating: identity on
        // unsupported layouts; obligations force original-clause
        // validation/replay downstream fail-closed.
        let dt_result = if conc_result.problem.has_datatype_sorts() {
            TransformationPipeline::new()
                .with(DtFlattener::new().with_verbose(verbose))
                .transform(conc_result.problem)
        } else {
            TransformationPipeline::new().transform(conc_result.problem)
        };
        let dt_changed = !dt_result.transform_memory().is_identity_grade();
        let rewrote_something = forwarding_changed || concretization_changed || dt_changed;
        if !dead_param_cost_bounded(&dt_result.problem) {
            if !rewrote_something {
                return Self::from_parts(
                    problem.clone(),
                    problem,
                    Box::new(IdentityBackTranslator),
                    false,
                );
            }
            return Self::from_parts(
                problem,
                dt_result.problem,
                Box::new(CompositeBackTranslator {
                    inner: vec![
                        dt_result.back_translator,
                        conc_result.back_translator,
                        forward_result.back_translator,
                    ],
                }),
                false,
            );
        }
        // The trailing cost-bounded arity slicer runs even when forwarding was
        // a no-op: select-only threaded-memory encodings (zero stores, e.g.
        // the read-only type-indexed table relations of the coroutine
        // "235-relation" instances) still carry dead memory params that the
        // slicer can collapse.
        let slice_result = TransformationPipeline::new()
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .transform(dt_result.problem);
        let slicing_changed = !slice_result.transform_memory().is_identity_grade();
        if !rewrote_something && !slicing_changed {
            return Self::from_parts(
                problem.clone(),
                problem,
                Box::new(IdentityBackTranslator),
                false,
            );
        }
        let summary = Self::from_parts(
            problem,
            slice_result.problem,
            Box::new(CompositeBackTranslator {
                inner: vec![
                    slice_result.back_translator,
                    dt_result.back_translator,
                    conc_result.back_translator,
                    forward_result.back_translator,
                ],
            }),
            false,
        );
        if verbose {
            let max_arity = |p: &ChcProblem| {
                p.predicates()
                    .iter()
                    .map(|pred| pred.arity())
                    .max()
                    .unwrap_or(0)
            };
            let full_arity = |p: &ChcProblem| {
                p.predicates()
                    .iter()
                    .map(|pred| pred.arity())
                    .sum::<usize>()
            };
            safe_eprintln!(
                "Portfolio: array-forwarding-only preprocessing: preds {} -> {}, max arity {} -> {}, full arity {} -> {} ({:?})",
                summary.original_problem.predicates().len(),
                summary.transformed_problem.predicates().len(),
                max_arity(&summary.original_problem),
                max_arity(&summary.transformed_problem),
                full_arity(&summary.original_problem),
                full_arity(&summary.transformed_problem),
                t_start.elapsed()
            );
        }
        summary
    }

    /// Build a BvToInt pipeline with a custom bit-decomposition width limit.
    ///
    /// CEGAR Phase 1: `decompose_limit = 0` (UF-only, fastest but least precise)
    /// CEGAR Phase 2: `decompose_limit = 64` (full decomposition, precise)
    ///
    /// Used for CEGAR-style refinement of variable-variable bitwise operations
    /// (#8289). Phase 1 tries UF approximation first; if the solver returns
    /// Unknown and `had_bitwise_uf_fallback()` is true, Phase 2 re-runs with
    /// full bit-decomposition for improved precision.
    pub(crate) fn build_int_with_decompose_limit(
        problem: ChcProblem,
        verbose: bool,
        decompose_limit: u32,
    ) -> Self {
        // Stage -1: fixpoint condense superpass (--chc-no-condense disables)
        let condense_result = condense_stage(problem.clone(), verbose);

        // Stage 0 (+ item 4a array store forwarding, cheap no-op without stores)
        let pre_pipeline = TransformationPipeline::new()
            .with(ArrayStoreForwarder::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose));
        let pre_result = pre_pipeline.transform(condense_result.problem);

        let dt_pipeline =
            TransformationPipeline::new().with(DtFlattener::new().with_verbose(verbose));
        let dt_result = dt_pipeline.transform(pre_result.problem);

        let pipeline = TransformationPipeline::new()
            .with(
                BvToIntAbstractor::new()
                    .with_verbose(verbose)
                    .with_decompose_limit(decompose_limit),
            )
            .with(IntervalPropagator::new().with_verbose(verbose))
            .with(LocalVarEliminator::new().with_verbose(verbose))
            .with(DeadParamEliminator::new().with_verbose(verbose))
            .with(portfolio_clause_inliner(&problem, verbose));
        let result = pipeline.transform(dt_result.problem);
        if verbose {
            safe_eprintln!(
                "Portfolio: BvToInt (decompose_limit={}) preprocessing: {} clauses -> {}",
                decompose_limit,
                problem.clauses().len(),
                result.problem.clauses().len()
            );
        }
        let bv_abstracted = problem_contains_recursive_bv_sorts(&problem);
        let back_translator: Box<dyn BackTranslator> = Box::new(CompositeBackTranslator {
            inner: vec![
                result.back_translator,
                dt_result.back_translator,
                pre_result.back_translator,
                condense_result.back_translator,
            ],
        });
        Self::from_parts(problem, result.problem, back_translator, bv_abstracted)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::TransformObligation;

    #[test]
    fn shared_condense_translator_delegates_ground_translation() {
        let translator =
            SharedCondenseBackTranslator(Arc::new(Mutex::new(Box::new(IdentityBackTranslator))));
        let derivation = crate::ground_derivation::GroundDerivation::default();

        let translated = translator
            .translate_ground_derivation(&derivation)
            .expect("identity delegate must preserve the derivation");

        assert!(translated.is_empty());
        assert_eq!(translator.ground_translation_name(), "identity");
    }

    /// #8419: sort_contains_recursive_bv must detect BV inside DT constructors.
    #[test]
    fn test_sort_contains_recursive_bv_inside_dt() {
        use crate::{ChcDtConstructor, ChcDtSelector};
        use std::sync::Arc;

        let dt_sort = ChcSort::Datatype {
            name: "OptionBV8".to_string(),
            constructors: Arc::new(vec![
                ChcDtConstructor {
                    name: "None".to_string(),
                    selectors: vec![],
                },
                ChcDtConstructor {
                    name: "Some".to_string(),
                    selectors: vec![ChcDtSelector {
                        name: "val".to_string(),
                        sort: ChcSort::BitVec(8),
                    }],
                },
            ]),
        };

        assert!(
            sort_contains_recursive_bv(&dt_sort),
            "should detect BV(8) inside DT constructor"
        );
    }

    #[test]
    fn test_sort_contains_recursive_bv_pure_int_dt() {
        use crate::{ChcDtConstructor, ChcDtSelector};
        use std::sync::Arc;

        let dt_sort = ChcSort::Datatype {
            name: "Pair".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "mk".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "fst".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "snd".to_string(),
                        sort: ChcSort::Int,
                    },
                ],
            }]),
        };

        assert!(
            !sort_contains_recursive_bv(&dt_sort),
            "pure Int DT should not be detected as containing BV"
        );
    }

    #[test]
    fn preprocess_summary_persists_identity_transform_memory() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("P", vec![ChcSort::BitVec(8)]);

        let summary = PreprocessSummary::build_bv_native(problem, false);

        assert_eq!(summary.transform_memory.transform(), "identity");
        assert!(summary.transform_memory.is_reversible());
        assert!(summary.transform_memory.unsafe_backtranslation_complete());
        assert!(!summary.transform_memory.safe_requires_original_validation());
    }

    /// Item 4a: the large-BV+array-DAG skip branch must now run the bounded
    /// store-forwarding pass + a trailing DeadParamEliminator so threaded
    /// memory arrays are sliced (arity collapse), while the slow general
    /// pipeline stays skipped.
    #[test]
    fn build_bv_native_large_dag_runs_store_forwarding_and_slices_arity() {
        use crate::{ChcExpr, ChcVar, ClauseBody, HornClause};

        let arr = || ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        let n_preds = 130usize;
        let sorts = vec![ChcSort::BitVec(8), arr(), arr(), arr(), arr()];
        let preds: Vec<_> = (0..n_preds)
            .map(|k| problem.declare_predicate(&format!("P{k}"), sorts.clone()))
            .collect();

        let b = ChcVar::new("b", ChcSort::BitVec(8));
        let ms: Vec<ChcVar> = (1..=4)
            .map(|j| ChcVar::new(format!("m{j}"), arr()))
            .collect();
        let t = ChcVar::new("t", arr());
        let y = ChcVar::new("y", ChcSort::Int);
        let args: Vec<ChcExpr> = std::iter::once(ChcExpr::var(b.clone()))
            .chain(ms.iter().map(|m| ChcExpr::var(m.clone())))
            .collect();

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::BitVec(0, 8))),
            ClauseHead::Predicate(preds[0], args.clone()),
        ));
        // 8 parallel hop edges per predicate pair -> >1024 clauses. Each hop
        // writes a memory cell through a clause-local temporary and reads it
        // back (the threaded-memory shape).
        for k in 1..n_preds {
            for c in 0..8i128 {
                let constraint = ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(t.clone()),
                        ChcExpr::store(
                            ChcExpr::var(ms[0].clone()),
                            ChcExpr::Int(7),
                            ChcExpr::Int(c),
                        ),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(y.clone()),
                        ChcExpr::select(ChcExpr::var(t.clone()), ChcExpr::Int(7)),
                    ),
                );
                problem.add_clause(HornClause::new(
                    ClauseBody::new(vec![(preds[k - 1], args.clone())], Some(constraint)),
                    ClauseHead::Predicate(preds[k], args.clone()),
                ));
            }
        }
        // Query keeps only the BV counter live.
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(preds[n_preds - 1], args.clone())],
                Some(ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::BitVec(5, 8))),
            ),
            ClauseHead::False,
        ));

        assert!(problem.predicates().len() > 128 && problem.clauses().len() > 1024);
        assert!(problem.has_bv_sorts() && problem.has_array_sorts());

        let summary = PreprocessSummary::build_bv_native(problem, false);
        assert!(!summary.bv_abstracted);
        for pred in summary.transformed_problem.predicates() {
            assert!(
                pred.arity() <= 1,
                "large-DAG lane must slice dead memory arrays: {} arity {}",
                pred.name,
                pred.arity()
            );
        }
        // Safe answers must still be validated against the original clauses.
        assert!(!summary.transform_memory.is_identity_grade());
    }

    /// Item 4 lanes wiring: the standalone forwarding-only constructor must
    /// slice threaded-memory arity exactly like the large-DAG skip branch,
    /// WITHOUT the >128-preds / >1024-clauses size gate (the raw acyclic BMC
    /// lanes call it on problems of any size).
    #[test]
    fn build_array_forwarding_only_slices_threaded_memory_arity() {
        use crate::{ChcExpr, ChcVar, ClauseBody, HornClause};

        let arr = || ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        let sorts = vec![ChcSort::Int, arr(), arr()];
        let preds: Vec<_> = (0..3)
            .map(|k| problem.declare_predicate(&format!("P{k}"), sorts.clone()))
            .collect();

        let x = ChcVar::new("x", ChcSort::Int);
        let m1 = ChcVar::new("m1", arr());
        let m2 = ChcVar::new("m2", arr());
        let t = ChcVar::new("t", arr());
        let y = ChcVar::new("y", ChcSort::Int);
        let args: Vec<ChcExpr> = vec![
            ChcExpr::var(x.clone()),
            ChcExpr::var(m1.clone()),
            ChcExpr::var(m2.clone()),
        ];

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
            ClauseHead::Predicate(preds[0], args.clone()),
        ));
        for k in 1..3usize {
            // Write through a clause-local temp, read it back: the
            // threaded-memory shape forwarding folds to a scalar.
            let constraint = ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(t.clone()),
                    ChcExpr::store(ChcExpr::var(m1.clone()), ChcExpr::Int(7), ChcExpr::Int(3)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::select(ChcExpr::var(t.clone()), ChcExpr::Int(7)),
                ),
            );
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(preds[k - 1], args.clone())], Some(constraint)),
                ClauseHead::Predicate(preds[k], args.clone()),
            ));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(preds[2], args.clone())],
                Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(5))),
            ),
            ClauseHead::False,
        ));

        let summary = PreprocessSummary::build_array_forwarding_only(problem, false);
        assert!(!summary.bv_abstracted);
        // Safe answers must still be validated against the original clauses.
        assert!(!summary.transform_memory.is_identity_grade());
        assert!(summary.transform_memory.unsafe_backtranslation_complete());
        for pred in summary.transformed_problem.predicates() {
            assert!(
                pred.arity() <= 1,
                "forwarding-only lane must slice dead memory arrays: {} arity {}",
                pred.name,
                pred.arity()
            );
        }
    }

    /// Select-only shapes (zero stores) still get the trailing cost-bounded
    /// arity slicer: forwarding no-ops but dead threaded memory params are
    /// collapsed (the coroutine "235-relation" instances carry read-only
    /// table arrays without a single store).
    #[test]
    fn build_array_forwarding_only_slices_dead_params_without_stores() {
        use crate::{ChcExpr, ChcVar, ClauseBody, HornClause};

        let arr = || ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        let sorts = vec![ChcSort::Int, arr()];
        let p0 = problem.declare_predicate("P0", sorts.clone());
        let p1 = problem.declare_predicate("P1", sorts);

        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);
        let m = ChcVar::new("m", arr());
        let args = |v: &ChcVar| vec![ChcExpr::var(v.clone()), ChcExpr::var(m.clone())];

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
            ClauseHead::Predicate(p0, args(&x)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p0, args(&x))],
                Some(ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
                )),
            ),
            ClauseHead::Predicate(p1, args(&y)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p1, args(&x))],
                Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(5))),
            ),
            ClauseHead::False,
        ));

        let summary = PreprocessSummary::build_array_forwarding_only(problem, false);
        assert!(!summary.transform_memory.is_identity_grade());
        assert!(summary.transform_memory.unsafe_backtranslation_complete());
        for pred in summary.transformed_problem.predicates() {
            assert!(
                pred.arity() <= 1,
                "slicer must drop the dead array param even without stores: {} arity {}",
                pred.name,
                pred.arity()
            );
        }
    }

    /// No-array problems short-circuit to an identity-grade summary (the raw
    /// acyclic lanes then behave exactly as before).
    #[test]
    fn build_array_forwarding_only_identity_without_arrays() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::BitVec(8)]);

        let summary = PreprocessSummary::build_array_forwarding_only(problem, false);
        assert!(summary.transform_memory.is_identity_grade());
        assert_eq!(summary.transformed_problem.predicates().len(), 1);
    }

    /// Multi-predicate linear chain for graph-collapse routing tests.
    fn multi_pred_chain_problem() -> ChcProblem {
        let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Mid x))))
(assert (forall ((x Int)) (=> (Mid x) (Loop x))))
(assert (forall ((x Int) (y Int))
    (=> (and (Loop x) (< x 10) (= y (+ x 1))) (Loop y))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#;
        crate::parser::ChcParser::parse(input).expect("parse multi-pred chain")
    }

    /// The explicit OFF path (kill-switch AY_GRAPH_COLLAPSE=0) is deterministic
    /// and applies no contraction — it is the pre-rank-6 baseline pipeline.
    /// (The default is now ON after the gate battery: 120-sample 60->64/120,
    /// 0 wrong; the default build is covered by the `on` test below.)
    #[test]
    fn graph_collapse_off_path_matches_default_build() {
        let problem = multi_pred_chain_problem();
        let off1 = PreprocessSummary::build_with_graph_collapse(problem.clone(), false, false);
        let off2 = PreprocessSummary::build_with_graph_collapse(problem, false, false);
        assert_eq!(
            format!("{:?}", off1.transformed_problem.clauses()),
            format!("{:?}", off2.transformed_problem.clauses()),
        );
        assert_eq!(
            off1.transformed_problem.predicates().len(),
            off2.transformed_problem.predicates().len(),
        );
    }

    /// AY_GRAPH_COLLAPSE on: the multi-predicate chain collapses below the
    /// flag-off predicate count and the transform memory still demands
    /// original validation for Safe answers with complete Unsafe replay.
    #[test]
    fn graph_collapse_on_contracts_chain_and_keeps_original_validation() {
        let problem = multi_pred_chain_problem();
        let off = PreprocessSummary::build_with_graph_collapse(problem.clone(), false, false);
        let on = PreprocessSummary::build_with_graph_collapse(problem, false, true);

        assert!(
            on.transformed_problem.predicates().len() <= off.transformed_problem.predicates().len(),
            "graph collapse must not add predicates: off={} on={}",
            off.transformed_problem.predicates().len(),
            on.transformed_problem.predicates().len()
        );

        assert!(on.transform_memory.validates_original());
        assert!(on.transform_memory.safe_requires_original_validation());
        assert!(on.transform_memory.unsafe_backtranslation_complete());
    }

    /// SPLIT-SYM runs after the condense reachability fixpoint. A control
    /// value used only by the query therefore creates a headless split clone
    /// late in preprocessing; the final reachability pass must remove that
    /// query and reconstruct the clone as false in the original model.
    #[test]
    fn final_reachability_prunes_late_headless_split_query() {
        use crate::pdr::{InvariantModel, PdrConfig, PredicateInterpretation};
        use crate::{ChcVar, ClauseBody, HornClause};

        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        // Keep the split control value away from argument zero so PC-SPLIT
        // cannot expose the unreachable clone before the condense fixpoint.
        let summary_pred =
            problem.declare_predicate("Summary", vec![array_sort.clone(), ChcSort::Int]);
        let array = ChcVar::new("a", array_sort);
        let args = |tag| vec![ChcExpr::var(array.clone()), ChcExpr::Int(tag)];

        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(summary_pred, args(0)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(summary_pred, args(0))]),
            ClauseHead::Predicate(summary_pred, args(1)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(summary_pred, args(1))]),
            ClauseHead::Predicate(summary_pred, args(1)),
        ));
        problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
            summary_pred,
            args(2),
        )])));

        let original = problem.clone();
        let summary = PreprocessSummary::build_with_graph_collapse(problem, false, false);
        assert!(
            summary
                .transformed_problem
                .predicates()
                .iter()
                .any(|predicate| predicate.name.contains("__ssym")),
            "the regression must exercise the late SPLIT-SYM clone path"
        );
        assert!(
            summary.transformed_problem.queries().next().is_none(),
            "the headless split-summary query must be removed"
        );
        assert!(
            summary.transformed_problem.has_query_evidence(),
            "queryless preprocessing must retain pruned-query evidence"
        );

        let mut transformed_model = InvariantModel::new();
        for predicate in summary.transformed_problem.predicates() {
            let vars = predicate
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| {
                    ChcVar::new(
                        format!("__p{}_a{index}", predicate.id.index()),
                        sort.clone(),
                    )
                })
                .collect();
            transformed_model.set(
                predicate.id,
                PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
            );
        }
        let translated = summary
            .back_translator
            .translate_validity(transformed_model);
        assert!(
            crate::engines::validate_external_invariant_model(
                &original,
                &translated,
                &PdrConfig::default(),
            )
            .expect("exact original-model validation must complete"),
            "the backtranslated queryless model must prove the original Safe problem"
        );
    }

    #[test]
    fn preprocess_summary_composes_bv_to_int_transform_memory() {
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("P", vec![ChcSort::BitVec(8)]);
        let x = crate::ChcVar::new("x", ChcSort::BitVec(8));
        problem.add_clause(crate::HornClause::query(crate::ClauseBody::new(
            vec![(pred, vec![crate::ChcExpr::var(x.clone())])],
            Some(crate::ChcExpr::eq(
                crate::ChcExpr::var(x),
                crate::ChcExpr::BitVec(0, 8),
            )),
        )));

        let summary = PreprocessSummary::build_int_only(problem, false);
        let obligation_names: Vec<_> = summary
            .transform_memory
            .obligations()
            .iter()
            .map(TransformObligation::name)
            .collect();

        assert_eq!(summary.transform_memory.transform(), "composite");
        assert!(summary.transform_memory.safe_requires_original_validation());
        assert!(summary.transform_memory.unsafe_backtranslation_complete());
        assert!(
            obligation_names.contains(&"bv-to-int-model-backtranslation"),
            "BvToInt preprocessing memory must retain model reconstruction obligations: {obligation_names:?}"
        );
        assert!(
            obligation_names.contains(&"original-validation-on-safe"),
            "BvToInt preprocessing memory must record original SAFE validation obligation: {obligation_names:?}"
        );
    }
}
