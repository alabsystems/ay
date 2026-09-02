// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause inlining transformation for CHC problems.
//!
//! This module implements clause inlining based on Eldarica's ClauseInliner.
//! It identifies non-recursive predicates with unique definitions and inlines
//! their bodies into clauses that use them, reducing the number of predicates.
//!
//! # Example
//!
//! Given:
//! ```text
//! Init(x) ⇐ true                    ; fact clause
//! Loop(x) ⇐ Init(x)                 ; single-use intermediate
//! Loop(x+1) ⇐ Loop(x), x < 10       ; self-loop
//! false ⇐ Loop(x), x ≥ 10           ; query
//! ```
//!
//! After inlining Init:
//! ```text
//! Loop(0) ⇐ true                    ; inlined: Init(0) → body of Init clause
//! Loop(x+1) ⇐ Loop(x), x < 10       ; unchanged
//! false ⇐ Loop(x), x ≥ 10           ; unchanged
//! ```
//!
//! # Reference
//!
//! Based on Eldarica: `reference/eldarica/src/main/scala/lazabs/horn/preprocessor/ClauseInliner.scala`

use crate::{ChcExpr, ChcProblem, ClauseBody, ClauseHead, HornClause, Predicate, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

mod back_translator;
mod clause_ops;
mod multi_def;

pub(crate) use back_translator::accept_profile_enabled;
use back_translator::InliningBackTranslator;

use super::{TransformationResult, Transformer};

/// Global counter for fresh variable generation to avoid name collisions.
static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Generate a fresh variable name with the given prefix.
fn fresh_var_name(prefix: &str) -> String {
    let count = FRESH_COUNTER.fetch_add(1, Ordering::SeqCst);
    format!("{prefix}__inline_{count}")
}

/// Kill switch for derivation-chain expansion (#chc25-deriv-expansion).
///
/// Default-enabled; set `AY_CHC_DISABLE_DERIV_EXPANSION` to any value other
/// than `0` to fall back to the pre-expansion behavior (composite derivation
/// entries left for content re-resolution → Unknown). Matches the
/// `AY_CHC_DISABLE_*` convention used by condense/pc_split/split_sym.
pub(super) fn deriv_expansion_enabled() -> bool {
    // B15: typed A/B switch (`ab_switches`); the never-set env read is gone.
    crate::ab_switches::get().deriv_expansion
}

/// One inlined-predicate application composed into a surviving clause.
///
/// Records exactly what the invalidity back-translator needs to rebuild the
/// intermediate derivation entry that inlining collapsed away. All
/// `PredicateId`s and clause structure are in the inliner's INPUT (pre-
/// compaction) space, so the reconstructed entries can be re-mapped by the
/// downstream (condense / pc_split) back-translators.
#[derive(Clone, Debug)]
pub(super) struct CompositionStep {
    /// The predicate that was inlined at this step.
    pub(super) inlined_pred: PredicateId,
    /// The arguments this predicate was called with, expressed in the
    /// COMPOSITE clause's variable space. Reading their concrete model values
    /// (from the composite derivation entry's `instances`) yields this
    /// predicate's argument values at the derivation step.
    pub(super) call_args: Vec<ChcExpr>,
    /// The defining clause used to inline `inlined_pred` (its head is
    /// `inlined_pred`). Determines the reconstructed entry's premise structure.
    pub(super) def_clause: HornClause,
    /// Index of `def_clause` in the inliner INPUT clause list, when stably
    /// known (single unique-def pass). Threaded into the reconstructed entry's
    /// `incoming_clause` so the downstream index-remapping back-translators
    /// carry it to an original clause. `None` ⇒ the reconstructed transition
    /// entry has no stable index and the whole expansion fails closed.
    pub(super) def_input_index: Option<usize>,
    /// How to REBUILD each fresh linking variable this step introduced, by
    /// evaluation rather than by search: `(fresh_var, defining_expression)`,
    /// with the defining expression in the variable space of the call site
    /// (the caller's variables, or fresh variables an EARLIER step in the same
    /// composition already defines — so a fixpoint over the whole set resolves
    /// the chain topologically).
    ///
    /// Inlining existentially projects these variables out of the surviving
    /// clause, and the ground derivation over that clause therefore carries no
    /// value for them; without a recorded definition the back-translator has to
    /// SOLVE for them, which re-enters the very theory gap the transforms exist
    /// to avoid. Only head-argument positions are recorded here; a definition's
    /// BODY-LOCAL variables are covered by [`Self::var_renames`] instead.
    ///
    /// Soundness: this is value SYNTHESIS, never evidence. The reconstructed
    /// derivation is still decided by `validate_ground_derivation` against the
    /// ORIGINAL clauses, so a wrong definition can only get the expansion
    /// REJECTED, never accepted.
    pub(super) linking_defs: Vec<(crate::ChcVar, ChcExpr)>,
    /// The COMPLETE variable rename this step applied to the defining clause:
    /// `(def_clause_var_name, composite_space_expression)`.
    ///
    /// [`Self::linking_defs`] covers only the fresh head-argument linking
    /// variables. This covers EVERY variable of the definition, including its
    /// BODY-LOCALS — the ones an original clause constrains only through an
    /// ITE, a tester or a disjunction, which no equality names and no premise
    /// pins. Those are existential in the ORIGINAL clause, but in the COMPOSITE
    /// they are ordinary named variables, so the level-BMC model assigns them.
    /// Recording the rename is what lets ground back-translation read that
    /// witness back instead of sort-defaulting a value it cannot derive, which
    /// is exactly what falsified the conjunct the counterexample satisfied.
    ///
    /// Soundness: identical to `linking_defs` — synthesis, never evidence. The
    /// value's PROVENANCE is an over-approximating transformed problem, which
    /// is precisely why nothing trusts it: it is written into an environment
    /// that `validate_ground_derivation` then re-evaluates against the ORIGINAL
    /// clauses. A wrong value makes some conjunct read false or some link
    /// disagree; either way the expansion is REJECTED.
    pub(super) var_renames: Vec<(String, ChcExpr)>,
}

/// Composition trace for a single surviving clause: the ordered chain of
/// inlined-predicate applications `apply_defs_tracked` composed into it.
///
/// Soundness: this is only a HINT used to OFFER a reconstructed derivation
/// chain. Every reconstructed entry is independently re-validated by the SMT
/// counterexample kernel against the ORIGINAL clauses; a wrong/stale trace can
/// only yield Spurious/Unknown, never a wrong `unsat`.
#[derive(Clone, Debug)]
pub(super) struct ClauseTrace {
    /// Index of the tracked clause in the inliner INPUT clause list.
    pub(super) c0_input_index: usize,
    /// The pre-inlining clause `C₀` (head = the composite clause's head).
    /// `None` until the clause is first inlined into.
    pub(super) original_clause: Option<HornClause>,
    /// The composite clause `apply_defs_tracked` produced (head = `C₀`'s head, body
    /// collapsed, constraint = accumulated linking equalities). Its constraint
    /// determines every intermediate predicate's argument values given the
    /// surviving endpoints, so the back-translator recovers them by SMT even
    /// when the engine model did not retain the fresh-variable assignments.
    pub(super) composite_clause: Option<HornClause>,
    /// Per inlined predicate: how to reconstruct its derivation entry.
    /// A predicate inlined more than once (non-path composition) poisons the
    /// trace instead of silently overwriting.
    pub(super) steps: FxHashMap<PredicateId, CompositionStep>,
    /// When set, expansion must fail closed for this clause (ambiguous or
    /// multi-pass composition that cannot be safely reconstructed).
    pub(super) poisoned: bool,
}

impl ClauseTrace {
    fn new(c0_input_index: usize) -> Self {
        Self {
            c0_input_index,
            original_clause: None,
            composite_clause: None,
            steps: FxHashMap::default(),
            poisoned: false,
        }
    }

    /// True when this trace records at least one composition and is usable.
    fn is_composite(&self) -> bool {
        !self.poisoned && self.original_clause.is_some() && !self.steps.is_empty()
    }

    /// Whether another inlining round may compose into this trace while
    /// retaining a one-level, ground-backtranslatable expansion.
    fn is_uncomposed(&self) -> bool {
        !self.poisoned && self.original_clause.is_none()
    }
}

/// Clause inlining preprocessor.
///
/// Inlines non-recursive predicates to reduce the number of predicates
/// in the CHC problem. Has two phases:
///
/// **Phase 1 (unique-definition):** Inlines predicates with exactly one
/// defining clause. This always reduces or preserves clause count.
///
/// **Phase 2 (multi-definition, Z3-style):** Inlines predicates with up to
/// `max_multi_defs` defining clauses, provided they appear in at most
/// `max_multi_tail_uses` tail positions across all clauses. This trades
/// clause count for predicate count: each use site expands to N clauses
/// (one per definition), but the predicate is eliminated.
///
/// Reference: Z3's `mk_rule_inliner` (`reference/z3/src/muz/transforms/dl_mk_rule_inliner.cpp`)
pub(crate) struct ClauseInliner {
    /// Maximum constraint size after inlining to prevent blowup.
    constraint_size_limit: usize,
    /// Maximum number of definitions for multi-def inlining (Z3 uses 4).
    max_multi_defs: usize,
    /// Maximum number of tail occurrences for multi-def inlining (Z3 uses 1).
    max_multi_tail_uses: usize,
    /// Enable verbose output.
    verbose: bool,
    /// Preserve predicates that occur directly in query bodies.
    ///
    /// The current invalidity back-translator does not reconstruct the extra
    /// derivation node needed when an inlined query-body predicate witnesses
    /// an Unsafe result. Portfolio preprocessing enables this conservative
    /// mode so BMC/PDR counterexamples validate against the original query.
    preserve_query_body_predicates: bool,
    /// Golem `SimpleNodeEliminator` candidate rule for multi-definition
    /// inlining (graph-collapse mode, AY_GRAPH_COLLAPSE):
    /// contract a predicate vertex when `|in| * |out| <= |in| + |out|`
    /// (so the def×use cross product never grows the clause count),
    /// restricted to linear in/out clauses, instead of the Z3-style
    /// `max_multi_defs`/`max_multi_tail_uses` caps.
    /// Reference: `reference/golem/src/transformers/NodeEliminator.cc`.
    graph_collapse_node_rule: bool,
}

impl Default for ClauseInliner {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseInliner {
    /// Create a new clause inliner with default settings.
    pub(crate) fn new() -> Self {
        Self {
            constraint_size_limit: 10000,
            max_multi_defs: 8,
            max_multi_tail_uses: 2,
            verbose: false,
            preserve_query_body_predicates: false,
            graph_collapse_node_rule: false,
        }
    }

    /// Enable or disable verbose output.
    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Do not inline predicates that appear directly in query bodies.
    pub(crate) fn preserve_query_body_predicates(mut self) -> Self {
        self.preserve_query_body_predicates = true;
        self
    }

    /// Select multi-definition candidates with golem's `SimpleNodeEliminator`
    /// rule (`|in| * |out| <= |in| + |out|` over linear clauses) instead of
    /// the Z3-style caps. Used by the graph-collapse preprocessing pass
    /// (AY_GRAPH_COLLAPSE=1).
    pub(crate) fn with_graph_collapse_node_rule(mut self) -> Self {
        self.graph_collapse_node_rule = true;
        self
    }

    /// Inline non-recursive clauses in the problem.
    ///
    /// Returns only the transformed problem (without back-translation info).
    /// Used by tests; production code uses `Transformer::transform` which
    /// also produces a back-translator.
    #[cfg(test)]
    pub(crate) fn inline(&self, problem: &ChcProblem) -> ChcProblem {
        self.inline_tracked(problem).0
    }

    /// Inline non-recursive clauses and return both the simplified problem
    /// and the defining clauses for each inlined predicate (for back-translation).
    /// Result of inlining: transformed problem, definitions for back-translation,
    /// a mapping from new (compacted) predicate IDs to original IDs, and the
    /// per-surviving-clause composition traces (keyed by FINAL clause index)
    /// used to expand collapsed derivation entries back onto the input clauses.
    /// The final component records declarations that were already absent from
    /// the INPUT clause graph before inlining. Predicate compaction removes
    /// those declarations, so validity back-translation must restore them.
    fn inline_tracked(
        &self,
        problem: &ChcProblem,
    ) -> (
        ChcProblem,
        Vec<(PredicateId, HornClause)>,
        FxHashMap<PredicateId, PredicateId>,
        FxHashMap<usize, ClauseTrace>,
        Option<Vec<usize>>,
        Vec<Predicate>,
    ) {
        let mut clauses: Vec<HornClause> = problem.clauses().to_vec();
        let mut inlined_defs: Vec<(PredicateId, HornClause)> = Vec::new();
        // Composition traces, aligned 1:1 with `clauses` throughout. Each
        // clause starts tracking its own INPUT index; retains/maps below keep
        // the alignment.
        let mut traces: Vec<ClauseTrace> = (0..clauses.len()).map(ClauseTrace::new).collect();
        // Whether `traces` still records genuine INPUT clause indices. The
        // ground-enabled multi-def path preserves this exactly; the legacy
        // kill-switch path retains its old fail-closed reset below.
        let mut traces_aligned = true;

        // Phase 1: Unique-definition inlining (Eldarica-style).
        self.inline_unique_defs(&mut clauses, &mut inlined_defs, &mut traces);

        // Phase 2: Multi-definition inlining (Z3-style).
        // Part of #6047: reduces 4-predicate ay_watched to 1 predicate (matching Z3).
        let (multi_def_clauses, multi_def_rewritten) =
            self.inline_multi_def(&clauses, &mut inlined_defs, &mut traces);
        clauses = multi_def_clauses;
        if multi_def_rewritten {
            if crate::ground_derivation::ground_backtranslation_enabled() {
                // Multi-def expansion retained exact caller/definition source
                // indices. Run the cleanup through the same trace-aware path
                // as phase 1 instead of its former untracked private loop.
                self.inline_unique_defs(&mut clauses, &mut inlined_defs, &mut traces);
            } else {
                // Preserve the kill-switch path exactly: without ground trace
                // tracking, a multi-def rewrite invalidates clause alignment.
                traces = (0..clauses.len()).map(ClauseTrace::new).collect();
                traces_aligned = false;
                self.inline_unique_defs(&mut clauses, &mut inlined_defs, &mut traces);
                // The cleanup traces start from post-multi-def OUTPUT indices,
                // not inliner INPUT indices. Keep legacy invalidity expansion
                // disabled for them as well as ground index translation.
                traces = (0..clauses.len()).map(ClauseTrace::new).collect();
            }
        }

        // Phase 3: Compact predicates — remove eliminated predicates from declarations
        // and remap IDs so PDR doesn't waste time on ghost predicates. Rebuilding
        // may prune simplified-false/duplicate clauses, so compaction filters
        // `traces` in lockstep to preserve final output-index alignment.
        let (new_problem, new_to_old, absent_input_predicates) =
            self.compact_predicates(problem, &mut clauses, &mut traces);
        debug_assert_eq!(
            traces.len(),
            new_problem.clauses().len(),
            "predicate compaction must retain one trace per emitted clause"
        );

        // Output clause index -> input clause index, for the ground
        // back-translator. `None` whenever the alignment was lost.
        let output_to_input =
            traces_aligned.then(|| traces.iter().map(|t| t.c0_input_index).collect::<Vec<_>>());
        let composition_traces: FxHashMap<usize, ClauseTrace> = traces
            .into_iter()
            .enumerate()
            .filter(|(_, t)| t.is_composite())
            .collect();
        debug_assert!(
            composition_traces
                .keys()
                .all(|index| *index < new_problem.clauses().len()),
            "composition trace key escaped the final compacted clause list"
        );
        debug_assert!(
            output_to_input
                .as_ref()
                .is_none_or(|map| map.len() == new_problem.clauses().len()),
            "output-to-input clause map is not aligned with compacted clauses"
        );
        debug_assert!(
            traces_aligned || composition_traces.is_empty(),
            "unaligned multi-def cleanup leaked output-index composition traces"
        );
        (
            new_problem,
            inlined_defs,
            new_to_old,
            composition_traces,
            output_to_input,
            absent_input_predicates,
        )
    }

    /// Build a compacted `ChcProblem` containing only predicates still referenced
    /// in the remaining clauses. Returns the new problem, a new→old ID mapping,
    /// and declarations absent from the INPUT clause graph.
    fn compact_predicates(
        &self,
        original: &ChcProblem,
        clauses: &mut Vec<HornClause>,
        traces: &mut Vec<ClauseTrace>,
    ) -> (
        ChcProblem,
        FxHashMap<PredicateId, PredicateId>,
        Vec<Predicate>,
    ) {
        debug_assert_eq!(
            clauses.len(),
            traces.len(),
            "clause/trace alignment was lost before predicate compaction"
        );
        // Collect predicate IDs still referenced in clauses.
        let mut used: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in clauses.iter() {
            for (pid, _) in &clause.body.predicates {
                used.insert(*pid);
            }
            if let Some(pid) = clause.head.predicate_id() {
                used.insert(pid);
            }
        }

        // A preceding transform can prune the final clause mentioning a
        // predicate while retaining its declaration. Such a declaration is
        // semantically unconstrained in THIS transform's input problem, so a
        // canonical `false` interpretation is an exact model completion. Keep
        // the declaration explicitly: compaction below removes it, and it has
        // no defining clause for the ordinary inlining back-translator to
        // reconstruct. Earlier back-translators remain free to overwrite this
        // value, and the composed result is validated on the original problem.
        let mut input_used: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in original.clauses() {
            for (pid, _) in &clause.body.predicates {
                input_used.insert(*pid);
            }
            if let Some(pid) = clause.head.predicate_id() {
                input_used.insert(pid);
            }
        }
        let absent_input_predicates: Vec<Predicate> = original
            .predicates()
            .iter()
            .filter(|pred| !input_used.contains(&pred.id))
            .cloned()
            .collect();

        let old_preds = original.predicates();
        let all_used = used.len() == old_preds.len();
        if all_used {
            // No predicates were eliminated — skip remapping.
            let mut new_problem = ChcProblem::new();
            for pred in old_preds {
                new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
            }
            let mut retained_traces = Vec::with_capacity(traces.len());
            for (clause, trace) in clauses.drain(..).zip(traces.drain(..)) {
                let before = new_problem.clauses().len();
                new_problem.add_clause(clause);
                if new_problem.clauses().len() > before {
                    retained_traces.push(trace);
                }
            }
            *traces = retained_traces;
            return (new_problem, FxHashMap::default(), absent_input_predicates);
        }

        // Build old→new mapping for used predicates (preserving order).
        let mut old_to_new: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
        let mut new_to_old: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
        let mut new_problem = ChcProblem::new();
        for pred in old_preds {
            if used.contains(&pred.id) {
                let new_id = new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
                old_to_new.insert(pred.id, new_id);
                new_to_old.insert(new_id, pred.id);
            }
        }

        if self.verbose {
            let eliminated = old_preds.len() - used.len();
            eprintln!(
                "CHC inlining: compacted {0} -> {1} predicates ({eliminated} eliminated)",
                old_preds.len(),
                used.len(),
            );
        }

        // Remap predicate IDs in all clauses and add them. `add_clause` may
        // simplify a constant-false expanded clause away (or deduplicate it).
        // Filter its trace in the SAME lockstep operation; otherwise every
        // later output clause selects the preceding clause's composition trace
        // and ground reconstruction addresses unrelated input rules.
        let mut retained_traces = Vec::with_capacity(traces.len());
        for (clause, trace) in clauses.drain(..).zip(traces.drain(..)) {
            let before = new_problem.clauses().len();
            new_problem.add_clause(Self::remap_clause_preds(&clause, &old_to_new));
            if new_problem.clauses().len() > before {
                retained_traces.push(trace);
            }
        }
        *traces = retained_traces;
        (new_problem, new_to_old, absent_input_predicates)
    }

    /// Remap predicate IDs in a clause using the given mapping.
    fn remap_clause_preds(
        clause: &HornClause,
        mapping: &FxHashMap<PredicateId, PredicateId>,
    ) -> HornClause {
        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let new_pid = mapping.get(pid).copied().unwrap_or(*pid);
                (new_pid, args.clone())
            })
            .collect();
        let new_body = ClauseBody::new(new_body_preds, clause.body.constraint.clone());
        let new_head = match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                let new_pid = mapping.get(pid).copied().unwrap_or(*pid);
                ClauseHead::Predicate(new_pid, args.clone())
            }
            ClauseHead::False => ClauseHead::False,
        };
        HornClause::new(new_body, new_head)
    }

    /// Phase 1: iteratively inline predicates with unique (single) definitions.
    fn inline_unique_defs(
        &self,
        clauses: &mut Vec<HornClause>,
        inlined_defs: &mut Vec<(PredicateId, HornClause)>,
        traces: &mut Vec<ClauseTrace>,
    ) {
        let mut iteration = 0;
        loop {
            iteration += 1;
            let unique_def_indices = self.find_unique_def_indices(clauses);
            if unique_def_indices.is_empty() {
                break;
            }
            let mut final_def_indices =
                self.extract_acyclic_def_indices(clauses, unique_def_indices);
            if crate::ground_derivation::ground_backtranslation_enabled() {
                let multi_candidates = self.multi_def_candidates(clauses);

                // A definition that only became inlineable after an earlier
                // round is often itself a composite clause. Flattening that
                // composite into another caller would require a nested trace;
                // the current ground translator deliberately represents one
                // composition layer. Likewise, composing into a caller that
                // already has a trace poisons its evidence.
                //
                // Keep the immediate neighbours of a multi-defined predicate
                // uncomposed as well. Phase 2 can then expand that predicate
                // with an exact one-level caller/definition trace instead of
                // inheriting a nested trace from phase 1.
                //
                // Keep those predicates explicit instead. This affects only
                // completeness/performance: the CHC remains equivalent, while
                // every transformed Unsafe derivation retains an exact
                // output→input proof expansion.
                final_def_indices.retain(|pred, clause_idx| {
                    traces
                        .get(*clause_idx)
                        .is_some_and(ClauseTrace::is_uncomposed)
                        && !clauses[*clause_idx]
                            .body
                            .predicates
                            .iter()
                            .any(|(body_pred, _)| multi_candidates.contains(body_pred))
                        && clauses.iter().enumerate().all(|(caller_idx, clause)| {
                            let calls_pred = clause
                                .body
                                .predicates
                                .iter()
                                .any(|(body_pred, _)| body_pred == pred);
                            !calls_pred
                                || (traces
                                    .get(caller_idx)
                                    .is_some_and(ClauseTrace::is_uncomposed)
                                    && !clause
                                        .body
                                        .predicates
                                        .iter()
                                        .any(|(body_pred, _)| multi_candidates.contains(body_pred))
                                    && clause
                                        .head
                                        .predicate_id()
                                        .map_or(true, |head| !multi_candidates.contains(&head)))
                        })
                });
            }
            if final_def_indices.is_empty() {
                break;
            }

            let final_defs: FxHashMap<PredicateId, HornClause> = final_def_indices
                .iter()
                .map(|(&pred_id, &clause_idx)| (pred_id, clauses[clause_idx].clone()))
                .collect();

            // `traces` stays aligned with `clauses` through every retain. For
            // each definition admitted by the one-level gate above,
            // c0_input_index is therefore its stable INPUT clause index.
            let def_input_indices: FxHashMap<PredicateId, usize> = final_def_indices
                .iter()
                .filter_map(|(&pred, &clause_idx)| {
                    traces
                        .get(clause_idx)
                        .map(|trace| (pred, trace.c0_input_index))
                })
                .collect();

            if self.verbose {
                let inlined_preds: Vec<_> =
                    final_defs.keys().map(|id| format!("P{}", id.0)).collect();
                safe_eprintln!(
                    "CHC inlining iteration {}: inlining {} predicates: {:?}",
                    iteration,
                    final_defs.len(),
                    inlined_preds
                );
            }

            // Record inlined definitions for back-translation. Normalize complex
            // head args to plain variables (#5295).
            for (&pred_id, clause) in &final_defs {
                let normalized = Self::normalize_head_for_back_translation(clause);
                inlined_defs.push((pred_id, normalized));
            }

            // Remove defining clauses and apply inlining to remaining clauses,
            // keeping `traces` aligned in lockstep.
            let inlined_heads: FxHashSet<PredicateId> = final_defs.keys().copied().collect();
            let keep: Vec<bool> = clauses
                .iter()
                .map(|c| {
                    c.head
                        .predicate_id()
                        .map_or(true, |h| !inlined_heads.contains(&h))
                })
                .collect();
            let mut ki = 0;
            clauses.retain(|_| {
                let k = keep[ki];
                ki += 1;
                k
            });
            let mut ki = 0;
            traces.retain(|_| {
                let k = keep[ki];
                ki += 1;
                k
            });

            let mut new_clauses = Vec::with_capacity(clauses.len());
            for (idx, c) in clauses.iter().enumerate() {
                let (nc, steps) = self.apply_defs_tracked(c, &final_defs, &def_input_indices);
                if !steps.is_empty() {
                    let trace = &mut traces[idx];
                    if trace.original_clause.is_none() {
                        trace.original_clause = Some(c.clone());
                        trace.composite_clause = Some(nc.clone());
                    } else {
                        // Composing again over an already-composed clause across
                        // passes: cannot safely reconstruct the merged chain.
                        trace.poisoned = true;
                    }
                    for s in steps {
                        if trace.steps.contains_key(&s.inlined_pred) {
                            trace.poisoned = true;
                        }
                        trace.steps.insert(s.inlined_pred, s);
                    }
                }
                new_clauses.push(nc);
            }
            *clauses = new_clauses;
        }
    }

    /// Find predicates with unique definitions (returns clause indices).
    ///
    /// A predicate P is uniquely defined if:
    /// 1. P appears in the head of exactly one clause
    /// 2. That clause has at most one body predicate (not self-recursive)
    /// 3. P is not FALSE (never inline the query head)
    fn find_unique_def_indices(&self, clauses: &[HornClause]) -> FxHashMap<PredicateId, usize> {
        let mut defs: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut blocked: FxHashSet<PredicateId> = FxHashSet::default();
        let query_body_preds =
            if self.preserve_query_body_predicates && Self::has_multi_defined_predicate(clauses) {
                Self::query_body_predicates(clauses)
            } else {
                FxHashSet::default()
            };

        for (idx, clause) in clauses.iter().enumerate() {
            let Some(head_pred) = clause.head.predicate_id() else {
                // Query clause (head is false) - skip
                continue;
            };

            if blocked.contains(&head_pred) {
                continue;
            }

            if query_body_preds.contains(&head_pred) {
                if self.verbose {
                    safe_eprintln!("CHC inlining: blocking P{} (query_body)", head_pred.0);
                }
                blocked.insert(head_pred);
                defs.remove(&head_pred);
                continue;
            }

            // Check if this clause is suitable for inlining
            let is_self_recursive = clause
                .body
                .predicates
                .iter()
                .any(|(id, _)| *id == head_pred);

            let has_multiple_body_preds = clause.body.predicates.len() > 1;

            if defs.contains_key(&head_pred) || has_multiple_body_preds || is_self_recursive {
                // Multiple definitions, or unsuitable clause - block this predicate
                if self.verbose {
                    let reason = if is_self_recursive {
                        "self_recursive"
                    } else if defs.contains_key(&head_pred) {
                        "multiple_definitions"
                    } else {
                        "multiple_body_preds"
                    };
                    safe_eprintln!("CHC inlining: blocking P{} ({})", head_pred.0, reason);
                }
                blocked.insert(head_pred);
                defs.remove(&head_pred);
            } else {
                // First (and potentially only) suitable definition
                defs.insert(head_pred, idx);
            }
        }

        // Filter out predicates whose definitions exceed size limits
        defs.retain(|_, &mut idx| {
            let clause = &clauses[idx];
            let constraint_size = clause.body.constraint.as_ref().map_or(0, Self::expr_size);
            constraint_size <= self.constraint_size_limit
        });

        if self.verbose {
            safe_eprintln!(
                "CHC inlining: {} clauses, {} predicates, {} candidates after filtering",
                clauses.len(),
                blocked.len() + defs.len(),
                defs.len()
            );
        }

        defs
    }

    fn has_multi_defined_predicate(clauses: &[HornClause]) -> bool {
        let mut head_count: FxHashMap<PredicateId, usize> = FxHashMap::default();
        for clause in clauses {
            if let Some(head_pred) = clause.head.predicate_id() {
                let count = head_count.entry(head_pred).or_insert(0);
                *count += 1;
                if *count > 1 {
                    return true;
                }
            }
        }
        false
    }

    pub(super) fn query_body_predicates(clauses: &[HornClause]) -> FxHashSet<PredicateId> {
        let mut query_body_preds = FxHashSet::default();
        for clause in clauses {
            if !matches!(clause.head, ClauseHead::False) {
                continue;
            }
            for (body_pred, _) in &clause.body.predicates {
                query_body_preds.insert(*body_pred);
            }
        }
        query_body_preds
    }

    /// Extract acyclic subset of definitions (using clause indices).
    ///
    /// Removes predicates that form cycles in their definitions to prevent
    /// infinite expansion during inlining.
    ///
    /// The algorithm proceeds bottom-up: first inline predicates whose body
    /// predicates are all non-candidates (leaf definitions), then inline
    /// predicates whose body predicates have already been inlined, and repeat.
    fn extract_acyclic_def_indices(
        &self,
        clauses: &[HornClause],
        unique_defs: FxHashMap<PredicateId, usize>,
    ) -> FxHashMap<PredicateId, usize> {
        let candidate_preds: FxHashSet<PredicateId> = unique_defs.keys().copied().collect();
        let mut remaining = unique_defs;
        let mut final_defs: FxHashMap<PredicateId, usize> = FxHashMap::default();

        let mut iterations = 0;
        let max_iterations = remaining.len() + 1; // Prevent infinite loop

        while !remaining.is_empty() && iterations < max_iterations {
            iterations += 1;

            // Find predicates whose body predicates are all either:
            // - Not candidates at all (external predicates)
            // - Already in final_defs (already scheduled for inlining)
            let can_inline: FxHashMap<PredicateId, usize> = remaining
                .iter()
                .filter(|(_, &idx)| {
                    let clause = &clauses[idx];
                    clause.body.predicates.iter().all(|(body_pred, _)| {
                        // Body pred is safe if it's not a candidate or already inlined
                        !candidate_preds.contains(body_pred) || final_defs.contains_key(body_pred)
                    })
                })
                .map(|(&p, &idx)| (p, idx))
                .collect();

            if can_inline.is_empty() {
                // All remaining predicates depend on other remaining predicates - cycle detected
                // Break the cycle by removing one predicate
                if let Some(cycle_breaker) = self.find_cycle_breaker_indices(clauses, &remaining) {
                    remaining.remove(&cycle_breaker);
                } else {
                    // No cycle breaker found, stop
                    break;
                }
            } else {
                // Remove can_inline from remaining and add to final_defs
                for pred in can_inline.keys() {
                    remaining.remove(pred);
                }
                final_defs.extend(can_inline);
            }
        }

        final_defs
    }

    /// Find a predicate to remove to break a cycle (using indices).
    ///
    /// Chooses a predicate that appears both as head and body in the remaining set.
    fn find_cycle_breaker_indices(
        &self,
        clauses: &[HornClause],
        remaining: &FxHashMap<PredicateId, usize>,
    ) -> Option<PredicateId> {
        let heads: FxHashSet<PredicateId> = remaining.keys().copied().collect();

        // Sort for deterministic cycle-breaker selection (#3060)
        let mut sorted_remaining: Vec<_> = remaining.iter().collect();
        sorted_remaining.sort_unstable_by_key(|(pid, _)| pid.index());
        for (_, &idx) in &sorted_remaining {
            let clause = &clauses[idx];
            for (body_pred, _) in &clause.body.predicates {
                if heads.contains(body_pred) {
                    return Some(*body_pred);
                }
            }
        }

        // Fallback: pick the smallest-index predicate for determinism
        sorted_remaining.first().map(|(pid, _)| **pid)
    }
}

impl Transformer for ClauseInliner {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let (
            new_problem,
            inlined_defs,
            new_to_old,
            composition_traces,
            output_to_input,
            absent_input_predicates,
        ) = self.inline_tracked(&problem);
        // The ground back-translator needs the INPUT clauses to rebuild and
        // self-validate the expanded derivation. Capturing the problem is only
        // worth its clone when the feature is on.
        let input_problem = crate::ground_derivation::ground_backtranslation_enabled()
            .then(|| std::sync::Arc::new(problem));
        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(InliningBackTranslator {
                inlined_defs,
                new_to_old,
                composition_traces,
                output_to_input,
                input_problem,
                absent_input_predicates,
            }),
        }
    }
}

#[cfg(test)]
mod tests;
