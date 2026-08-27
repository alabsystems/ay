// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! E-Matching module for quantifier instantiation.
//!
//! Implements pattern-based E-matching to instantiate universal quantifiers
//! by matching patterns against ground terms in the term store.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use ay_euf::EufModel;
use std::collections::BTreeMap;

/// Red zone size for `stacker::maybe_grow` in ematching recursion (#5612).
pub(super) const EMATCH_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for ematching recursion.
pub(super) const EMATCH_STACK_SIZE: usize = 1024 * 1024;

/// Maximum number of binding combinations in multi-trigger cross-product join.
/// Prevents combinatorial explosion when many candidate matches exist per trigger term.
const MAX_MULTI_TRIGGER_BINDINGS: usize = 1000;

/// Check if a term contains any quantifiers (forall or exists).
/// Used to return `unknown` for formulas with quantifiers that we can't fully handle.
///
/// Uses a visited set to avoid exponential re-traversal on DAG-structured terms.
/// Without memoization, deeply nested formulas (e.g., countbitstableoffbyone0128
/// with 128-bit BV + 256 stores) cause exponential blowup because shared
/// sub-terms are visited once per parent path.
pub(crate) fn contains_quantifier(terms: &TermStore, term: TermId) -> bool {
    let mut visited = HashSet::default();
    contains_quantifier_memo(terms, term, &mut visited)
}

fn contains_quantifier_memo(
    terms: &TermStore,
    term: TermId,
    visited: &mut HashSet<TermId>,
) -> bool {
    if !visited.insert(term) {
        return false;
    }
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) => true,
            TermData::Not(inner) => contains_quantifier_memo(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                contains_quantifier_memo(terms, *c, visited)
                    || contains_quantifier_memo(terms, *t, visited)
                    || contains_quantifier_memo(terms, *e, visited)
            }
            TermData::App(_, args) => args
                .iter()
                .any(|&arg| contains_quantifier_memo(terms, arg, visited)),
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, val)| contains_quantifier_memo(terms, *val, visited))
                    || contains_quantifier_memo(terms, *body, visited)
            }
            TermData::Const(_) | TermData::Var(_, _) => false,
            // Future TermData variants: conservatively assume no quantifiers.
            _ => false,
        }
    })
}

mod ground_terms;
mod matching;
mod pattern;
mod pattern_helpers;
mod persistent;
mod relevance;
mod substitution;
#[cfg(test)]
mod test_support;
pub(crate) use ground_terms::{
    collect_bool_uf_arg_terms, collect_ground_terms_by_sort, contains_fixed_interpreted_arithmetic,
    enumerative_instantiation,
};
use matching::{match_multi_trigger, match_pattern};
#[cfg(test)]
use pattern::extract_patterns;
pub(crate) use pattern::EqualityClasses;
use pattern::{extract_patterns_with_fallback, TermIndex};
#[cfg(test)]
use pattern::{EMatchArg, EMatchPattern};
#[cfg(test)]
use pattern_helpers::pattern_covered_vars;
pub(crate) use persistent::PersistentMatchState;
pub(crate) use relevance::{
    instance_features, relevance_config, score_instance, split_top_k, ModelStanding,
    RelevanceConfig, ScoredInstance,
};
#[cfg(test)]
use substitution::collect_free_var_names;
use substitution::instantiate_body;
pub(crate) use substitution::{mk_app_simplified, subst_vars, subst_vars_exact_qf};
#[cfg(test)]
use test_support::{perform_ematching, perform_ematching_with_config};

/// Configuration for E-matching instantiation limits.
///
/// These limits prevent infinite loops from self-triggering patterns like:
/// `(forall ((x Int)) (P (f x)))` with `(P (f (f (f a))))`.
///
/// Generation tracking provides cost-based filtering:
/// - Input problem terms have generation 0
/// - Terms from instantiation round N get generation = max(binding_generations) + 1
/// - Instantiation cost = weight + generation
/// - High-cost instantiations are deferred or blocked
///
/// Reference: Z3 smt/smt_enode.h:67, sat/smt/q_ematch.cpp:425-430
#[derive(Clone, Debug)]
pub(crate) struct EMatchingConfig {
    pub(crate) max_per_quantifier: usize,
    pub(crate) max_total: usize,
    pub(crate) eager_threshold: f64,
    pub(crate) lazy_threshold: f64,
    pub(crate) default_weight: f64,
}

impl Default for EMatchingConfig {
    fn default() -> Self {
        Self {
            max_per_quantifier: 1000,
            max_total: 10000,
            eager_threshold: 10.0,
            lazy_threshold: 20.0,
            default_weight: 1.0,
        }
    }
}

fn effective_quantifier_weight(
    terms: &TermStore,
    quantifier: TermId,
    config: &EMatchingConfig,
) -> f64 {
    terms
        .explicit_quantifier_weight(quantifier)
        .map_or(config.default_weight, f64::from)
}

/// Tracks generation (age) of terms for cost-based instantiation filtering.
///
/// Generation tracking prevents infinite instantiation loops more intelligently
/// than count limits by assigning a cost to each potential instantiation based
/// on how "deep" the matched terms are in the instantiation chain.
///
/// - Generation 0: Input problem terms
/// - Generation N: Terms created from instantiations where max binding generation was N-1
///
/// Reference: Z3 smt/smt_enode.h:67, qi_queue.cpp:127-134
#[derive(Clone, Debug, Default)]
pub(crate) struct GenerationTracker {
    /// Generation per term. Terms not in this map have generation 0.
    generations: HashMap<u32, u32>,
    /// Current round number (incremented each E-matching pass).
    current_round: u32,
}

impl GenerationTracker {
    /// Create a new generation tracker.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Get the generation of a term (0 if not tracked).
    pub(crate) fn get(&self, term: TermId) -> u32 {
        *self.generations.get(&term.0).unwrap_or(&0)
    }

    /// Set the generation of a term.
    pub(crate) fn set(&mut self, term: TermId, generation: u32) {
        // Don't store generation 0 to save memory
        if generation > 0 {
            self.generations.insert(term.0, generation);
        }
    }

    /// Get the maximum generation among a set of terms.
    pub(crate) fn max_generation(&self, terms: &[TermId]) -> u32 {
        terms.iter().map(|t| self.get(*t)).max().unwrap_or(0)
    }

    /// Compute instantiation cost: weight + max_binding_generation.
    pub(crate) fn instantiation_cost(&self, binding: &[TermId], weight: f64) -> f64 {
        weight + f64::from(self.max_generation(binding))
    }

    /// Start a new round of E-matching.
    pub(crate) fn next_round(&mut self) {
        self.current_round += 1;
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
impl GenerationTracker {
    pub(crate) fn current_round(&self) -> u32 {
        self.current_round
    }
}

/// Per-family demand-instantiation tally (M0' demand-campaign instrumentation).
///
/// A "family" (M0' cheap proxy; the real classifier lands in M1) is the pair
/// (source quantifier `TermId`, head trigger symbol name). `gen_hist` records, per
/// generation level, how many asserted instances of this family were minted at
/// that generation — the per-family generation histogram read off the
/// [`GenerationTracker`]'s assigned generations.
#[derive(Clone, Debug, Default)]
pub(crate) struct FamilyDemand {
    /// Instances eagerly instantiated (cost <= eager_threshold, new to the memo).
    pub asserted: u64,
    /// Instances deferred/parked (eager_threshold < cost <= lazy_threshold).
    pub parked: u64,
    /// Instances skipped/blocked at the cost gate (cost > lazy_threshold).
    pub blocked: u64,
    /// generation -> count of asserted instances minted at that generation.
    pub gen_hist: BTreeMap<u32, u64>,
}

/// Demand-driven-instantiation observation counters (M0' instrumentation).
///
/// PURE OBSERVATION — every field is written ONLY as a side effect of the
/// cost-gate branches inside [`perform_ematching_with_generations`], and NOTHING
/// here is ever read back to steer instantiation, ordering, or any verdict.
/// Deleting this struct wholesale would not change a single solve result (release
/// behavior byte-identical in effect). Surfaced under the `quantifier.demand.*`
/// statistics prefix via [`Self::write_statistics`].
#[derive(Clone, Debug, Default)]
pub(crate) struct DemandStats {
    /// Total asserted (eager) instances across all families.
    pub asserted: u64,
    /// Total parked (deferred) instances across all families.
    pub parked: u64,
    /// Total blocked (skipped at the cost gate) instances across all families.
    pub blocked: u64,
    /// Number of E-matching rounds that broke early on a budget/deadline
    /// (`max_total` / `max_per_quantifier` / `should_stop`).
    pub budget_break_rounds: u64,
    /// Aggregate (all-family) generation histogram: gen -> asserted-instance count.
    pub gen_hist: BTreeMap<u32, u64>,
    /// Per-family stats, keyed by (quantifier `TermId` raw, head trigger symbol).
    /// `BTreeMap` for deterministic ordering when surfaced.
    pub families: BTreeMap<(u32, String), FamilyDemand>,
}

impl DemandStats {
    fn family_mut(&mut self, quant: TermId, head: &str) -> &mut FamilyDemand {
        self.families
            .entry((quant.0, head.to_string()))
            .or_default()
    }

    /// Record one eagerly-asserted instance of `quant` (head symbol `head`) minted
    /// at generation `generation`.
    fn record_asserted(&mut self, quant: TermId, head: &str, generation: u32) {
        self.asserted += 1;
        *self.gen_hist.entry(generation).or_default() += 1;
        let fam = self.family_mut(quant, head);
        fam.asserted += 1;
        *fam.gen_hist.entry(generation).or_default() += 1;
    }

    /// Record one parked (deferred) instance of `quant` (head symbol `head`).
    fn record_parked(&mut self, quant: TermId, head: &str) {
        self.parked += 1;
        self.family_mut(quant, head).parked += 1;
    }

    /// Record one blocked (cost-gate-skipped) instance of `quant` (head `head`).
    fn record_blocked(&mut self, quant: TermId, head: &str) {
        self.blocked += 1;
        self.family_mut(quant, head).blocked += 1;
    }

    /// Merge a per-round delta into this cross-round accumulator (additive).
    pub(crate) fn merge(&mut self, other: &DemandStats) {
        self.asserted += other.asserted;
        self.parked += other.parked;
        self.blocked += other.blocked;
        self.budget_break_rounds += other.budget_break_rounds;
        for (g, c) in &other.gen_hist {
            *self.gen_hist.entry(*g).or_default() += c;
        }
        for (key, fd) in &other.families {
            let entry = self.families.entry(key.clone()).or_default();
            entry.asserted += fd.asserted;
            entry.parked += fd.parked;
            entry.blocked += fd.blocked;
            for (g, c) in &fd.gen_hist {
                *entry.gen_hist.entry(*g).or_default() += c;
            }
        }
    }

    /// Surface these counters into `stats` under the `quantifier.demand.*` prefix.
    /// PURE OUTPUT: reads the accumulated counters only.
    pub(crate) fn write_statistics(&self, stats: &mut crate::Statistics) {
        stats.set_int("quantifier.demand.asserted", self.asserted);
        stats.set_int("quantifier.demand.parked", self.parked);
        stats.set_int("quantifier.demand.blocked", self.blocked);
        stats.set_int(
            "quantifier.demand.budget_break_rounds",
            self.budget_break_rounds,
        );
        stats.set_int("quantifier.demand.families", self.families.len() as u64);
        let max_gen = self.gen_hist.keys().last().copied().unwrap_or(0);
        stats.set_int("quantifier.demand.max_generation", u64::from(max_gen));
        // Aggregate generation histogram of asserted instances. Bounded by the DT
        // deepening depth and deterministic (BTreeMap order).
        for (generation, count) in &self.gen_hist {
            stats.set_int(&format!("quantifier.demand.gen.{generation}"), *count);
        }
        // Per-head-trigger-symbol aggregation — the meaningful, stable half of the
        // (TermId, symbol) family key. Families sharing a head symbol are folded so
        // the surfaced keys carry no run-varying TermId.
        let mut by_head: BTreeMap<&str, (u64, u64, u64)> = BTreeMap::new();
        for ((_, head), fd) in &self.families {
            let entry = by_head.entry(head.as_str()).or_default();
            entry.0 += fd.asserted;
            entry.1 += fd.parked;
            entry.2 += fd.blocked;
        }
        for (head, (asserted, parked, blocked)) in by_head {
            stats.set_int(&format!("quantifier.demand.head.{head}.asserted"), asserted);
            stats.set_int(&format!("quantifier.demand.head.{head}.parked"), parked);
            stats.set_int(&format!("quantifier.demand.head.{head}.blocked"), blocked);
        }
    }
}

/// Exact provenance for a ground instance of an unconditionally asserted
/// universal. This is proof metadata only; solver decisions continue to use
/// [`EMatchingResult::instantiations`].
#[derive(Clone, Debug)]
pub(crate) struct ForallInstantiationProvenance {
    pub quantifier: TermId,
    pub binding: Vec<TermId>,
    pub instance: TermId,
}

/// Result of E-matching: instantiations plus soundness info.
pub(crate) struct EMatchingResult {
    /// Ground instantiations derived from quantified formulas.
    pub instantiations: Vec<TermId>,
    /// Exact quantifier roots for which at least one binding passed the
    /// instantiation cost gate in this round.
    ///
    /// This is provenance, not a completeness claim: callers use it to tell
    /// whether an existential was actually processed by E-matching.  Deriving
    /// that fact by comparing a separately recollected quantifier list against
    /// `uninstantiated_quantifiers` is unsound because NNF recollection can
    /// mint an equivalent quantifier with a different `TermId`.
    pub instantiated_quantifiers: HashSet<TermId>,
    /// True if any quantifier had no matching ground terms.
    /// When true and solver returns Sat, we must return Unknown instead.
    pub has_uninstantiated: bool,
    /// Set of quantifier term IDs that had no ground matches.
    /// Used by CEGQI to only add counterexample lemmas for uninstantiated quantifiers (#1939).
    pub uninstantiated_quantifiers: HashSet<TermId>,
    /// True if instantiation limit was reached.
    /// When true, result is incomplete and solver should return Unknown.
    pub reached_limit: bool,
    /// Deferred instantiations (cost > eager_threshold but <= lazy_threshold).
    pub deferred: Vec<DeferredInstantiation>,
    /// Updated generation tracker with new term generations.
    pub generation_tracker: GenerationTracker,
    /// Ground-instance roots (`body[t/x]` TermIds) that are provably valid in
    /// every model of the asserted problem: each is an instantiation of a
    /// Forall that is an UNCONDITIONALLY-asserted top-level conjunct (see
    /// [`collect_unconditional_foralls`]). This is the SOUND subset of
    /// [`Self::instantiations`] that the fail-closed conflict-verification gate
    /// may assert as `support_axioms` alongside a conflict — by universal
    /// instantiation each is entailed, so it can only CONFIRM a genuine
    /// conflict, never launder a spurious one. Every member's source quantifier
    /// is a `TermData::Forall` (Exists excluded) that is NOT nested under any
    /// `or`/`ite`/`=>`/`not` (disjunction/conditional Foralls excluded).
    pub unconditional_forall_roots: HashSet<TermId>,
    /// Source quantifier and positional binding for the sound subset above.
    /// A downstream proof producer still must authenticate the source as a
    /// direct problem assertion and re-check the exact substitution.
    pub unconditional_forall_instantiations: Vec<ForallInstantiationProvenance>,
    /// M0' demand-campaign instrumentation for THIS round (pure observation; see
    /// [`DemandStats`]). Never consulted by any solver decision.
    pub demand: DemandStats,
}

/// A deferred instantiation for later processing.
#[derive(Clone, Debug)]
pub(crate) struct DeferredInstantiation {
    /// The quantifier being instantiated.
    pub quantifier: TermId,
    /// The variable bindings (term IDs for each bound variable).
    pub binding: Vec<TermId>,
    /// The actual variable names in the quantifier body (needed for instantiation).
    pub var_names: Vec<String>,
}

/// A PARKED family instance for the M2+M3 demand lane (SHADOW-ONLY).
///
/// Produced at the E-matching cost gate when the demand lane is armed and a
/// binding of a *frontier-gated* family (M1 `SelfChainingDefinitional` /
/// `BridgeCycle`) would mint an instance whose generation exceeds the current
/// generation frontier `F`. Per DESIGN LAW #7 (park-not-drop) it is NOT skipped —
/// it is retained here, WITH its generation and binding terms, so that DESIGN LAW
/// #1 (unconditional under-frontier flush) can assert it verbatim once `F` bumps
/// past its generation, and DESIGN LAW #2 (fence drain) can flush the whole queue
/// directly (bypassing the seen-memo) before any Sat/Unknown conclusion.
///
/// Distinct from [`DeferredInstantiation`] (a COST-gate deferral,
/// `eager < cost <= lazy`): a parked instance is a FRONTIER-gate deferral, keyed
/// on its generation vs `F`, and it drives the demand loop's on-demand deepening.
#[derive(Clone, Debug)]
pub(crate) struct ParkedInstance {
    /// The quantifier being instantiated.
    pub quantifier: TermId,
    /// The variable bindings (term IDs for each bound variable).
    pub binding: Vec<TermId>,
    /// The actual variable names in the quantifier body (needed for instantiation).
    pub var_names: Vec<String>,
    /// The generation the instance WOULD carry once asserted
    /// (`max_binding_generation + 1`). The flush gate compares this to `F`.
    pub generation: u32,
    /// Head trigger symbol (for the per-family demand counters).
    /// Shadow-staged (M2+M3): consumed once the demand lane goes live.
    #[allow(dead_code)]
    pub head: String,
}

/// One round's demand-lane gate (SHADOW-ONLY; M2+M3). Passed into
/// [`perform_ematching_with_generations`] as `Some(..)` ONLY when the shadow
/// demand lane is armed; `None` on every production path (byte-identical).
///
/// It carries the current generation frontier `F`, the set of frontier-gated
/// quantifier raw ids (`TermId.0` of the M1 `SelfChainingDefinitional` /
/// `BridgeCycle` foralls), and a sink for instances parked this round. It NEVER
/// changes a verdict on its own: parking only removes an eager assertion (which
/// can never create a false UNSAT), and the parked instances are re-asserted by
/// the flush/fence before any conclusion.
pub(crate) struct DemandGate<'a> {
    /// Current generation frontier `F` (>= 1). An instance is asserted eagerly
    /// when its generation `<= F`, parked when `> F`.
    pub frontier: u32,
    /// Frontier-gated quantifier raw ids (M1 self-chaining / bridge-cycle).
    pub gated: &'a HashSet<u32>,
    /// Instances parked this round (LAW #7 sink).
    pub parked: &'a mut Vec<ParkedInstance>,
    /// Count of over-frontier instances parked (surfaced under
    /// `quantifier.demand.frontier_parked`).
    pub frontier_parked: u64,
    /// Diagnostic: max `would_be_gen` observed for a gated-family binding this
    /// round (0 if none). Reveals whether the recursive chaining actually reaches
    /// generation > F.
    pub max_gated_gen: u32,
    /// Diagnostic: number of gated-family bindings that passed the seen gate.
    pub gated_bindings: u64,
    /// M4 (A0 no-drop conservation oracle): count of gated-family bindings that
    /// were NOT parked (generation `<= F`, so they proceeded to the normal
    /// eager/defer/assert path). Together with `frontier_parked` this partitions
    /// `gated_bindings` exactly — `gated_bindings == frontier_parked + gated_passed`
    /// — so a debug conservation assert can prove the gate never SILENTLY DROPS a
    /// gated binding (every one it sees is either parked or passed through).
    pub gated_passed: u64,
}

impl DeferredInstantiation {
    /// Instantiate this deferred entry, producing the actual term.
    ///
    /// This is used for promote-unsat (Phase D): we need the actual term
    /// to check if it would create a conflict under the current model.
    pub(crate) fn instantiate(&self, terms: &mut TermStore) -> Option<TermId> {
        // Get the body of the quantifier
        let body = match terms.get(self.quantifier) {
            TermData::Forall(_, b, _) => *b,
            TermData::Exists(_, b, _) => *b,
            _ => return None,
        };

        // Substitute the bindings into the body
        Some(instantiate_body(
            terms,
            body,
            &self.var_names,
            &self.binding,
        ))
    }
}

impl ParkedInstance {
    /// Instantiate this parked entry and TAG the resulting term (and its fresh
    /// subterms) with its parked generation (LAW #1 flush / LAW #4 charge-and-tag:
    /// a flushed instance is charged at exactly the generation it would have had
    /// been minted eagerly, so the frontier keeps gating deeper chains correctly —
    /// no gen-0 laundering). Returns the ground instance TermId.
    pub(crate) fn instantiate_and_tag(
        &self,
        terms: &mut TermStore,
        tracker: &mut GenerationTracker,
    ) -> Option<TermId> {
        let body = match terms.get(self.quantifier) {
            TermData::Forall(_, b, _) => *b,
            TermData::Exists(_, b, _) => *b,
            _ => return None,
        };
        let inst = instantiate_body(terms, body, &self.var_names, &self.binding);
        tracker.set(inst, self.generation);
        set_subterm_generations(terms, inst, self.generation, tracker);
        Some(inst)
    }
}

/// Perform E-matching with generation tracking for cost-based filtering.
///
/// Generation tracking assigns a "depth" to each term:
/// - Input terms have generation 0
/// - Terms created from instantiation get generation = max(binding_generations) + 1
///
/// Instantiation cost = weight + max_binding_generation.
/// - cost <= eager_threshold: instantiate immediately
/// - eager_threshold < cost <= lazy_threshold: defer for later
/// - cost > lazy_threshold: skip (blocked)
///
/// `should_stop` is polled every `STOP_CHECK_INTERVAL` bindings so a wall-clock
/// deadline or interrupt can break a single round before it materializes its
/// full per-round instantiation budget (up to `max_total` ~ 10000 instances).
/// On stop the round sets `reached_limit = true` and breaks out, which the
/// caller routes to `Unknown` (never to a final `Sat`). Removing instantiations
/// can only weaken the conjunction, so this can never produce a false UNSAT.
pub(crate) fn perform_ematching_with_generations(
    terms: &mut TermStore,
    assertions: &[TermId],
    config: &EMatchingConfig,
    mut tracker: GenerationTracker,
    euf_model: Option<&EufModel>,
    should_stop: &dyn Fn() -> bool,
    state: &mut PersistentMatchState,
    // M2+M3 demand lane (SHADOW-ONLY): `Some` only when the shadow demand lane is
    // armed. `None` on every production path — byte-identical.
    mut demand_gate: Option<&mut DemandGate<'_>>,
) -> EMatchingResult {
    // M2+M3 LAW #4 watermark: the term-store boundary at round entry. Any term a
    // gated-family binding references that was MINTED this round (TermId >= this)
    // must carry a generation > 0 — a gen-0 post-watermark binding term is the
    // laundering bug the charge-AND-tag pass closes. SHADOW-ONLY (consulted only
    // when `demand_gate` is Some, under a debug_assert).
    let demand_watermark = terms.len();

    let mut quantifiers = Vec::new();
    for &assertion in assertions {
        collect_quantifiers(terms, assertion, &mut quantifiers);
    }

    if quantifiers.is_empty() {
        return EMatchingResult {
            instantiations: vec![],
            instantiated_quantifiers: HashSet::default(),
            has_uninstantiated: false,
            uninstantiated_quantifiers: HashSet::default(),
            reached_limit: false,
            deferred: vec![],
            generation_tracker: tracker,
            unconditional_forall_roots: HashSet::default(),
            unconditional_forall_instantiations: Vec::new(),
            demand: DemandStats::default(),
        };
    }

    // SOUND support-axiom provenance: the Foralls that are UNCONDITIONALLY
    // asserted (top-level conjuncts of an asserted formula). Strictly narrower
    // than `quantifiers` — which flattens through `or`/`ite` and would surface
    // non-entailed Foralls. Only ground instances of these are tagged into
    // `unconditional_forall_roots` below; by universal instantiation each such
    // instance is true in every model of the problem.
    let mut unconditional_foralls: HashSet<TermId> = HashSet::default();
    for &assertion in assertions {
        collect_unconditional_foralls(terms, assertion, &mut unconditional_foralls);
    }
    let mut unconditional_forall_roots: HashSet<TermId> = HashSet::default();

    // (#auflia-disjunct-forall-false-unsat) SOUNDNESS GATE for instantiation
    // itself. Every instance this function returns is appended to `ctx.assertions`
    // as a TOP-LEVEL CONJUNCT by every caller (`add_ematching_instances`,
    // `dispatch.rs`, `run_post_cegqi_ematching`, the demand-lane flush), so the
    // instance must be a CONSEQUENCE OF THE PROBLEM, not merely of its source
    // quantifier. `collect_entailed_foralls` is the polarity-aware predicate for
    // that; `quantifiers` above is NOT (it flattens through `or`/`ite`/`=>`
    // without polarity and deliberately also surfaces `Exists`).
    let entailed_foralls: HashSet<TermId> = entailed_forall_set(terms, assertions);

    tracker.next_round();

    // Incrementally refresh the persisted ground-term index by walking only NEW
    // assertion roots (LI-1/LI-2). Equivalent to `TermIndex::new(terms, assertions)`
    // — the cfg(debug_assertions) differential canary asserts this every round.
    state.refresh_index(terms, assertions);

    // Incrementally fold only NEW explicit `(= a b)`/`(and ...)` atoms into the
    // persisted assertion-only equality classes (#3325 Gap 1, LI-7/LI-8), then
    // build the per-round WORKING copy: a clone augmented with EUF congruence.
    // The EUF congruence is applied ONLY to the clone and NEVER persisted (LI-6),
    // because the model changes per interleaved round and union-find cannot
    // un-merge.
    state.refresh_eqclasses(terms, assertions);
    let eqclasses = state.working_eqclasses(euf_model);
    let eqclasses_opt = if eqclasses.is_empty() {
        None
    } else {
        Some(&eqclasses)
    };

    // MATCHING. The bindings a single-trigger pattern produces are a pure function
    // of (candidate set, working eqclasses), but the per-candidate INSTANTIATION
    // outcome also depends on round-varying state (the cost gate, instantiation
    // budgets, deferred promotion). The "new-candidate-only" skip — re-match only NEW
    // candidates while the eqclass partition fingerprint is stable — was therefore not
    // instantiation-complete (it watermarks a candidate before its outcome is final),
    // and is now DISABLED: `begin_match_round` always returns `false`, so `is_new_candidate`
    // is never consulted and EVERY candidate is re-matched each round (see the long
    // rationale on `begin_match_round`). `eqclasses_stable` is consequently always false;
    // the watermark/replay branches below are retained but inert. The dominant
    // incremental win (the per-round index BUILD) is unaffected.
    let working_fp = eqclasses.partition_fingerprint();
    let eqclasses_stable = state.begin_match_round(working_fp);

    let mut instantiations = Vec::new();
    let mut deferred = Vec::new();
    let mut instantiated_quantifiers: HashSet<TermId> = HashSet::default();
    let mut unconditional_forall_instantiations = Vec::new();
    let mut per_quantifier_count: HashMap<TermId, usize> = HashMap::default();
    let mut reached_limit = false;
    // M0' demand-campaign instrumentation for this round. Written ONLY at the
    // cost-gate branches below; never read to steer any decision.
    let mut demand = DemandStats::default();

    // Poll the deadline/interrupt closure periodically inside the binding loop.
    // A single round can otherwise enumerate up to `config.max_total` bindings
    // (~10000) before the per-round budget check fires, overrunning the wall
    // clock. `bindings_processed` counts iterations across all quantifiers.
    const STOP_CHECK_INTERVAL: usize = 256;
    let mut bindings_processed: usize = 0;

    'outer: for &quant in &quantifiers {
        let trigger_groups = extract_patterns_with_fallback(terms, quant);
        let (quant_vars, body) = match terms.get(quant) {
            TermData::Forall(v, b, _) => (v.clone(), *b),
            // NEVER instantiate an existential here. Universal instantiation is
            // sound (`∀x.P(x) ⊨ P(t)`); existential instantiation is NOT
            // (`∃x.P(x) ⊭ P(t)` — it pins an arbitrary term as the witness).
            // Every caller of this function appends the returned instances to
            // `ctx.assertions` as top-level CONJUNCTS, so an existential
            // instance silently strengthens the problem and any UNSAT derived
            // from it may be a wrong answer.
            //
            // This produced a real one: the AUFLIA 20170829-Rodin file
            // `smt4579745768945200905.smt2` returns `unsat` where z3 and the
            // benchmark's own declared `:status` both say `sat`, with
            // `conflicts=0, decisions=0` — the refutation comes entirely from
            // conjoined instances, not from search. Found by the 2026-07-25
            // corpus scoreboard.
            //
            // Skipping is fail-closed in BOTH directions. The quantifier gets no
            // ground match, so it lands in `uninstantiated_quantifiers`, which
            // (a) leaves `ematching_has_exists` false — now truthful, since no
            // existential was instantiated — and (b) sets `has_uninstantiated`,
            // which blocks the `full_ematching_coverage` SAT certificate in
            // `result_mapping.rs`. So neither an unsound UNSAT nor an unsound
            // SAT can be built on top of it.
            //
            // The downstream `QuantifierEmatchingExistsIncomplete` guard
            // (#3593, result_mapping.rs:1503) stays as defense in depth; it was
            // a mitigation for instances that should never have been created.
            //
            // These existentials reach here only because the NNF Skolemizer has
            // no arm for a Boolean `=`/`xor`/`distinct` or an `ite` condition,
            // so an `exists` nested in one survives verbatim with no tracked
            // polarity. Handling those arms is the completeness follow-up;
            // refusing to instantiate is the soundness floor.
            TermData::Exists(..) => continue,
            _ => continue,
        };
        // (#auflia-disjunct-forall-false-unsat) NEVER instantiate a Forall that
        // the assertion set does not ENTAIL. Universal instantiation is sound as
        // an IMPLICATION (`∀x.body ⇒ body[t/x]`), but every caller conjoins the
        // returned instance as a top-level assertion, which asserts the
        // CONSEQUENT unconditionally. That is only licensed when `∀x.body` is
        // itself entailed — a top-level conjunct, a conjunct under `and`, a
        // negated `exists`, … A Forall reachable only under a positive `or`/`=>`
        // or an `ite` is a mere DISJUNCT: the problem does not entail it, so its
        // "instance" is a fabricated constraint that can refute a satisfiable
        // problem. Measured doing exactly that on six AUFLIA/20170829-Rodin
        // files (declared `sat`, confirmed `sat` by z3 and cvc5) whose
        // Skolemizer output `(forall x. (or (not (mAckn x)) (forall y. (not (dap
        // y x)))))` puts the INNER universal under a disjunction.
        //
        // Skipping is FAIL-CLOSED IN BOTH DIRECTIONS, exactly like the `Exists`
        // refusal above: the quantifier gets no ground match, so it lands in
        // `uninstantiated_quantifiers`, which sets `has_uninstantiated` and
        // thereby blocks the `full_ematching_coverage` SAT certificate in
        // `result_mapping.rs`, and routes it to the unhandled/MBQI lane. So
        // neither an unsound UNSAT nor an unsound SAT can be built on it.
        //
        // The sound way to USE such a quantifier is the guarded lemma
        // `(or (not Q) body[t/x])` — but `flatten_and_strip_quantifiers` drops
        // every quantifier-containing assertion before the ground solve, so a
        // guarded lemma would be discarded rather than used. Recovering these
        // instances therefore needs a real quantifier abstraction in the ground
        // solver; refusing to instantiate is the soundness floor until then.
        if !entailed_foralls.contains(&quant) {
            continue;
        }
        // Only ground instances of an UNCONDITIONALLY-asserted Forall are sound
        // to thread as conflict-verification support (the strict `and`-only walk
        // in `collect_unconditional_foralls` populates `unconditional_foralls`).
        // Any disjunction/ite-nested Forall is absent from `unconditional_foralls`
        // and excluded here. (Exists no longer needs excluding: it is skipped
        // outright above, so everything reaching this point is a Forall.)
        let quant_is_unconditional_forall = unconditional_foralls.contains(&quant);
        // Sorts of the bound variables, aligned with the trigger-group binding
        // indices (which follow the quantifier's declared var order — see
        // `extract_patterns_with_fallback`). Used by the matcher's sort-
        // coherence gate: a pattern variable may only bind a ground term of
        // its declared sort (width-polymorphic symbols like `bvmul` otherwise
        // admit cross-width bindings whose instantiation builds ill-sorted
        // terms).
        let var_sorts: Vec<Sort> = quant_vars.iter().map(|(_, sort)| sort.clone()).collect();

        let quant_count = per_quantifier_count.entry(quant).or_insert(0);
        let quantifier_weight = effective_quantifier_weight(terms, quant, config);
        // LI-INC-3: replay the epoch matched-binding record. When the eqclasses are
        // stable and this round skips `quant`'s OLD candidates, the per-round
        // `instantiated_quantifiers` firewall input must still reflect that a PRIOR
        // round of this epoch matched a binding for `quant` — exactly as the HEAD
        // full-rematch path would (it rematches the old candidates and re-marks it).
        // We RE-EVALUATE the cost gate against the CURRENT tracker over the
        // remembered bindings, so the mark is dropped if a binding value's
        // generation has since lifted its cost over the lazy threshold (HEAD-exact,
        // never an unsafe over-mark). New-candidate matches below additionally
        // re-mark. When eqclasses changed, the watermark was cleared and every
        // candidate is re-matched anyway, so the record is not consulted.
        let mut quantifier_instantiated_this_round = false;
        if eqclasses_stable {
            for old_binding in state.epoch_matched_bindings_for(quant) {
                let cost = tracker.instantiation_cost(old_binding, quantifier_weight);
                if cost <= config.lazy_threshold {
                    instantiated_quantifiers.insert(quant);
                    quantifier_instantiated_this_round = true;
                    break;
                }
            }
        }

        for (phase_idx, groups) in [&trigger_groups.primary, &trigger_groups.fallback]
            .iter()
            .enumerate()
        {
            if phase_idx == 1 && quantifier_instantiated_this_round {
                break;
            }

            for trigger_group in *groups {
                let vars = &trigger_group.var_names;
                // M0' family key (cheap proxy): head trigger symbol of this group.
                // Constant across the group's bindings; computed once. Pure
                // observation — used only to bucket the demand counters.
                let head_sym: &str = trigger_group
                    .patterns
                    .first()
                    .map_or("", |p| p.symbol.name());

                // Collect all bindings for this trigger group.
                // Single trigger: fast path using direct candidate lookup. When the
                // eqclasses are stable, restrict to NEW candidates (not yet matched
                // under this fingerprint); otherwise match all. Record every
                // candidate we run the matcher on so a later stable round skips it.
                // Multi-trigger: join across all patterns (always full re-match — the
                // cross-product join over per-pattern candidate sets is bounded by
                // MAX_MULTI_TRIGGER_BINDINGS and is not incrementalized here).
                let bindings: Vec<Vec<TermId>> = if trigger_group.patterns.len() == 1 {
                    let pattern = &trigger_group.patterns[0];
                    let sym = pattern.symbol.name();
                    // Borrow the persisted index only for the duration of binding
                    // collection so `state` is free to be mutated afterward in this
                    // iteration. Collect the candidates we will record as matched.
                    let mut matched_now: Vec<TermId> = Vec::new();
                    let bindings = {
                        let index = state.index();
                        let candidates = index.get_by_symbol(sym);
                        candidates
                            .iter()
                            .filter(|&&gt| {
                                // A no_mbqi ("E-matching only") quantifier — the
                                // Hilbert-`choose` combined axiom `forall i,j.
                                // P(i,j) => P(chosen)` — must NOT be discharged by
                                // a ground term the SOLVER invented: ay's
                                // `add_diagonal_forall_instances` completeness pass
                                // manufactures `P(c,c)` for every constant `c`, and
                                // MBQI/CEGQI materialize `P(model-value,..)` apps —
                                // matching one would establish `P(chosen)` with NO
                                // genuine program witness (proving more than Verus,
                                // which is trigger-only).
                                //
                                // The TERM-ID WATERMARK (terms.is_synthesized) is
                                // the exact discriminator: `set_synthesis_watermark`
                                // runs at the top of the quantifier loop, BEFORE
                                // Skolemization, the diagonal pass, and MBQI/CEGQI
                                // value materialization, and a hash-consed id never
                                // changes — so an authored witness (`f2(7, 8)`, and
                                // equally the diagonal-arg `cnatf2(10, 10)`) keeps
                                // its pre-watermark id even if a synthesis pass
                                // re-materializes the same term, while every
                                // solver-invented app allocates post-watermark.
                                // Generation is NOT usable here (a re-materialized
                                // witness reappears at generation>0), and a blanket
                                // diagonal-shape refusal that used to sit alongside
                                // the watermark refused genuine AUTHORED diagonal
                                // witnesses too — `assert(cnatf2(10, 10))` before a
                                // `choose` over `cnatf2` left the marked axiom
                                // unfireable and a Verus-verified case unknown
                                // (choose.rs `test_refine2_tuple`). Shape is not
                                // provenance; the watermark is.
                                // Sound: restricting instantiation only loses proofs,
                                // never yields a wrong-UNSAT.
                                if terms.is_no_mbqi(quant) && terms.is_synthesized(gt) {
                                    false
                                } else if eqclasses_stable && !state.is_new_candidate(sym, gt) {
                                    // Already matched under this eqclass fingerprint:
                                    // its binding is unchanged and already seen.
                                    false
                                } else {
                                    matched_now.push(gt);
                                    true
                                }
                            })
                            .filter_map(|&gt| {
                                match_pattern(terms, pattern, gt, &var_sorts, eqclasses_opt)
                            })
                            .collect()
                    };
                    // Record the candidates we matched against this round so a later
                    // stable round can skip them (the index borrow has ended).
                    for gt in matched_now {
                        state.record_matched_candidate(sym, gt);
                    }
                    bindings
                } else {
                    match_multi_trigger(
                        terms,
                        &trigger_group.patterns,
                        state.index(),
                        &var_sorts,
                        eqclasses_opt,
                    )
                };

                for binding in bindings {
                    bindings_processed += 1;
                    if bindings_processed.is_multiple_of(STOP_CHECK_INTERVAL) && should_stop() {
                        // Deadline/interrupt fired mid-round. Mark the round
                        // incomplete so the caller classifies the result as
                        // Unknown (QuantifierRoundLimit), never a final Sat.
                        reached_limit = true;
                        break 'outer;
                    }

                    if instantiations.len() >= config.max_total {
                        reached_limit = true;
                        break 'outer;
                    }

                    if *quant_count >= config.max_per_quantifier {
                        reached_limit = true;
                        break;
                    }

                    // Compute instantiation cost based on generation
                    let cost = tracker.instantiation_cost(&binding, quantifier_weight);

                    if cost > config.lazy_threshold {
                        // A cost-blocked binding is an incomplete E-matching
                        // campaign, even when a cheaper binding for the same
                        // quantifier was accepted. Mark the limit so every SAT
                        // mapping fails closed; per-quantifier "matched once"
                        // is not coverage of the skipped ground application.
                        reached_limit = true;
                        // M0': count the skip where it physically occurs,
                        // before the seen memo (high-cost bindings never enter
                        // that memo).
                        demand.record_blocked(quant, head_sym);
                        continue;
                    }

                    // LI-5: a binding with cost <= lazy_threshold marks the
                    // quantifier instantiated THIS round, EXACTLY as the HEAD
                    // full-rebuild path does (which uses a fresh per-round seen
                    // and therefore always reaches the mark on the first
                    // occurrence). We mark BEFORE the persistent-seen gate so a
                    // binding suppressed as a cross-round duplicate still counts
                    // as instantiated — keeping has_uninstantiated /
                    // uninstantiated_quantifiers HEAD-identical, which is the
                    // input to the conservative Unknown firewall. The persistent
                    // seen gate below then only skips the duplicated WORK.
                    instantiated_quantifiers.insert(quant);
                    quantifier_instantiated_this_round = true;
                    // LI-INC-3: remember this matched binding (it passed the cost
                    // gate) so a later stable round — which skips this now-OLD
                    // candidate — can re-evaluate the cost gate over it and re-mark
                    // the quantifier HEAD-identically without re-running the matcher.
                    state.record_epoch_matched_binding(quant, binding.clone());

                    let key = (quant, binding.clone());
                    if !state.seen_insert(key) {
                        // Already produced (this round or an earlier same-state
                        // round). instantiate_body is idempotent (hash-consed), so
                        // re-deriving contributes no new TermId. Skip the work.
                        continue;
                    }

                    // M2+M3 demand lane (SHADOW-ONLY) — LAW #7 park-not-drop.
                    // When the demand lane is armed and this binding belongs to a
                    // frontier-gated family (M1 self-chaining / bridge-cycle), an
                    // instance whose generation would exceed the current frontier
                    // `F` is PARKED (retained with its generation + binding), never
                    // asserted this round. It is re-asserted verbatim by the flush
                    // (LAW #1) once `F` bumps past its generation, or by the fence
                    // drain (LAW #2) before any conclusion. This is what stops the
                    // geometric level-0 round-chaining that buries the depth-<=F
                    // refutation. The binding is already `seen`-inserted above, so
                    // it is not re-derived (and thus not re-parked) next round.
                    //
                    // SOUNDNESS: removing an eager assertion can only WEAKEN the
                    // conjunction, never produce a false UNSAT; and because parking
                    // sets `has_deferred` (LAW #3) via the parked queue, a Sat is
                    // never finalized while instances remain parked.
                    if let Some(gate) = demand_gate.as_deref_mut() {
                        let would_be_gen =
                            tracker.max_generation(&binding).saturating_add(1).max(1);
                        if gate.gated.contains(&quant.0) {
                            gate.gated_bindings += 1;
                            gate.max_gated_gen = gate.max_gated_gen.max(would_be_gen);
                            // LAW #4 watermark check: no gen-0 laundering. Every
                            // binding term this round MINTED (TermId >= watermark)
                            // must be generation-tagged; a gen-0 one would let the
                            // recursive chain re-enter as level-0 forever.
                            debug_assert!(
                                binding.iter().all(|b| {
                                    (b.0 as usize) < demand_watermark || tracker.get(*b) > 0
                                }),
                                "LAW #4 gen-0 laundering: a gated binding references a \
                                 post-watermark term with generation 0 (quant {})",
                                quant.0
                            );
                        }
                        if gate.gated.contains(&quant.0) && would_be_gen > gate.frontier {
                            gate.parked.push(ParkedInstance {
                                quantifier: quant,
                                binding: binding.clone(),
                                var_names: vars.clone(),
                                generation: would_be_gen,
                                head: head_sym.to_string(),
                            });
                            gate.frontier_parked += 1;
                            demand.record_parked(quant, head_sym);
                            continue;
                        }
                        // M4 (A0 no-drop conservation): a gated binding that was NOT
                        // parked (generation <= F) proceeds to the normal path below.
                        // Counting it here makes `gated_bindings == frontier_parked +
                        // gated_passed` hold exactly, so the round-level conservation
                        // debug_assert can prove nothing was silently dropped.
                        if gate.gated.contains(&quant.0) {
                            gate.gated_passed += 1;
                        }
                    }

                    if cost > config.eager_threshold {
                        // M0': parked (deferred, eager < cost <= lazy threshold).
                        demand.record_parked(quant, head_sym);
                        deferred.push(DeferredInstantiation {
                            quantifier: quant,
                            binding: binding.clone(),
                            var_names: vars.clone(),
                        });
                        continue;
                    }

                    // LAW #4 (charge-AND-tag) watermark: record the term-store
                    // boundary BEFORE instantiation so the freshly-minted subterm
                    // chain (`tl self`, `sum(tl self)`, ...) can be generation-
                    // tagged below. SHADOW-ONLY (only read when `demand_gate` is
                    // Some), so production is unaffected.
                    let pre_inst_len = terms.len();

                    let inst = instantiate_body(terms, body, vars, &binding);

                    // Set generation: max(binding_generations) + 1, minimum 1
                    let max_binding_gen = tracker.max_generation(&binding);
                    let new_gen = max_binding_gen.saturating_add(1).max(1);
                    tracker.set(inst, new_gen);
                    set_subterm_generations(terms, inst, new_gen, &mut tracker);

                    // M2+M3 LAW #4 (bidirectional generation charge-AND-tag,
                    // SHADOW-ONLY): the stock `set_subterm_generations` above is a
                    // no-op here — `inst` was just tagged, so its guard returns
                    // before recursing — which is the "gen-0 laundering hole": the
                    // recursive selector chain a defining-axiom instance mints
                    // (`tl self`, `sum(tl self)`, deeper) keeps generation 0, so the
                    // frontier gate never sees the chain grow and the geometric
                    // level-0 minting is unbounded. In the shadow demand lane, tag
                    // every term MINTED by this instantiation (TermId at/after the
                    // pre-instantiation watermark) with `new_gen` so the next round's
                    // match on the chain carries `new_gen + 1` and the frontier gate
                    // engages. Pre-existing input terms (`self`, `final`, and the
                    // ground `sum(self)`/`sum(final)` in the goal) keep their gen 0,
                    // so the depth-1 instances stay UNDER F=1 and are asserted. This
                    // never runs on production (`demand_gate` is None there).
                    if demand_gate.is_some() {
                        let end = terms.len();
                        for idx in pre_inst_len..end {
                            let t = TermId::new(idx as u32);
                            if tracker.get(t) == 0 {
                                tracker.set(t, new_gen);
                            }
                        }
                    }

                    instantiations.push(inst);
                    // M0': asserted (eager instantiation) at generation `new_gen`.
                    demand.record_asserted(quant, head_sym, new_gen);
                    // Tag the sound support-axiom subset: `inst = body[binding/x]`
                    // is a ground instance of the top-level-conjunct Forall
                    // `quant`, hence entailed and true in every problem-model.
                    if quant_is_unconditional_forall {
                        debug_assert!(
                            matches!(terms.get(quant), TermData::Forall(..))
                                && unconditional_foralls.contains(&quant),
                            "support-axiom root's source quant must be an \
                             unconditionally-asserted Forall (soundness invariant)"
                        );
                        unconditional_forall_roots.insert(inst);
                        unconditional_forall_instantiations.push(ForallInstantiationProvenance {
                            quantifier: quant,
                            binding: binding.clone(),
                            instance: inst,
                        });
                    }
                    *quant_count += 1;
                }
            }
        }
    }

    #[cfg(debug_assertions)]
    state.assert_seen_consistent();

    // MANDATORY incremental-matching differential canary. Recompute the
    // firewall-critical `instantiated_quantifiers` set with a FULL per-round
    // re-match (every candidate, no new-candidate skip, no epoch replay) over the
    // SAME quantifiers + working eqclasses, and assert it equals the incrementally
    // computed set. A divergence here would mean the new-candidate skip dropped a
    // match the full path finds (the only way incremental matching could change a
    // result), so this MUST hold. Gated behind the `ematching-differential` feature
    // so production builds keep the perf win; enabled by the verification suite.
    // Only run the canary when the round completed normally: the instantiation
    // budget limits (`max_total`/`max_per_quantifier`) and the deadline/`should_stop`
    // break out of the loop early and skip the marking for later quantifiers, which
    // the unlimited full recomputation would still mark — a benign, expected
    // difference under truncation, not a matching divergence.
    #[cfg(feature = "ematching-differential")]
    if !reached_limit {
        let full_instantiated = compute_full_instantiated_quantifiers(
            terms,
            &quantifiers,
            &tracker,
            config,
            eqclasses_opt,
            state.index(),
        );
        debug_assert_eq!(
            instantiated_quantifiers, full_instantiated,
            "incremental matching diverged from full re-match: instantiated_quantifiers \
             differs (new-candidate skip / epoch replay dropped or added a match)"
        );
    }

    // Compute which quantifiers had no ground matches (#1939)
    let uninstantiated_quantifiers: HashSet<TermId> = quantifiers
        .iter()
        .copied()
        .filter(|q| !instantiated_quantifiers.contains(q))
        .collect();
    let has_uninstantiated = !uninstantiated_quantifiers.is_empty();

    // M0': a round that was incomplete because of a budget/deadline or a
    // cost-blocked binding sets `reached_limit`. Record it as one budget-break
    // round; merged additively across the round loop.
    demand.budget_break_rounds = u64::from(reached_limit);

    EMatchingResult {
        instantiations,
        instantiated_quantifiers,
        has_uninstantiated,
        uninstantiated_quantifiers,
        reached_limit,
        deferred,
        generation_tracker: tracker,
        unconditional_forall_roots,
        unconditional_forall_instantiations,
        demand,
    }
}

/// Differential-canary helper: recompute the `instantiated_quantifiers` set the
/// way the HEAD full-rematch path would — matching EVERY candidate for every
/// quantifier (no new-candidate skip, no epoch replay), marking a quantifier
/// instantiated for any binding whose cost is `<= lazy_threshold`, and applying
/// the same primary/fallback phase rule. Used only under the
/// `ematching-differential` feature to assert the incremental path is identical.
#[cfg(feature = "ematching-differential")]
fn compute_full_instantiated_quantifiers(
    terms: &TermStore,
    quantifiers: &[TermId],
    tracker: &GenerationTracker,
    config: &EMatchingConfig,
    eqclasses_opt: Option<&EqualityClasses>,
    index: &TermIndex,
) -> HashSet<TermId> {
    let mut instantiated: HashSet<TermId> = HashSet::default();
    for &quant in quantifiers {
        let quantifier_weight = effective_quantifier_weight(terms, quant, config);
        let trigger_groups = extract_patterns_with_fallback(terms, quant);
        let var_sorts: Vec<Sort> = match terms.get(quant) {
            TermData::Forall(v, _, _) | TermData::Exists(v, _, _) => {
                v.iter().map(|(_, sort)| sort.clone()).collect()
            }
            _ => continue,
        };
        let mut quantifier_instantiated_this_round = false;
        for (phase_idx, groups) in [&trigger_groups.primary, &trigger_groups.fallback]
            .iter()
            .enumerate()
        {
            if phase_idx == 1 && quantifier_instantiated_this_round {
                break;
            }
            for trigger_group in *groups {
                let bindings: Vec<Vec<TermId>> = if trigger_group.patterns.len() == 1 {
                    let pattern = &trigger_group.patterns[0];
                    index
                        .get_by_symbol(pattern.symbol.name())
                        .iter()
                        .filter_map(|&gt| {
                            match_pattern(terms, pattern, gt, &var_sorts, eqclasses_opt)
                        })
                        .collect()
                } else {
                    match_multi_trigger(
                        terms,
                        &trigger_group.patterns,
                        index,
                        &var_sorts,
                        eqclasses_opt,
                    )
                };
                for binding in bindings {
                    let cost = tracker.instantiation_cost(&binding, quantifier_weight);
                    if cost > config.lazy_threshold {
                        continue;
                    }
                    instantiated.insert(quant);
                    quantifier_instantiated_this_round = true;
                }
            }
        }
    }
    instantiated
}

/// Set generation for all subterms of a term (if they don't already have one).
///
/// Early-returns if the term already has a non-zero generation to avoid redundant work
/// and prevent setting generation on pre-existing input terms.
fn set_subterm_generations(
    terms: &TermStore,
    term: TermId,
    generation: u32,
    tracker: &mut GenerationTracker,
) {
    // Skip if term already has a generation (either from input or previous instantiation)
    if tracker.get(term) != 0 {
        return;
    }
    tracker.set(term, generation);

    match terms.get(term) {
        TermData::App(_, args) => {
            for &arg in args {
                set_subterm_generations(terms, arg, generation, tracker);
            }
        }
        TermData::Not(inner) => set_subterm_generations(terms, *inner, generation, tracker),
        TermData::Ite(c, t, e) => {
            set_subterm_generations(terms, *c, generation, tracker);
            set_subterm_generations(terms, *t, generation, tracker);
            set_subterm_generations(terms, *e, generation, tracker);
        }
        TermData::Let(bindings, body) => {
            for (_, v) in bindings {
                set_subterm_generations(terms, *v, generation, tracker);
            }
            set_subterm_generations(terms, *body, generation, tracker);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            set_subterm_generations(terms, *body, generation, tracker);
        }
        TermData::Const(_) | TermData::Var(_, _) => {}
        // Future TermData variants: skip (no subterms to set).
        _ => {}
    }
}

/// Collect all quantified formulas from a term.
///
/// Applies NNF (Negation Normal Form) conversion for negated quantifiers:
///   NOT(exists x. phi) → forall x. NOT(phi)
///   NOT(forall x. phi) → exists x. NOT(phi)
/// This is critical for soundness: without it, E-matching instantiates the body
/// with wrong polarity, producing false UNSAT results (#3593).
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
/// Collect the set of top-level App symbol names that a pattern requires a
/// ground term to carry in order to (possibly) match. For a pattern `S(...)`
/// the required symbol is `S`; nested patterns `S(.., T(..), ..)` additionally
/// require `T` to appear somewhere ground. We collect the FULL set of symbols
/// appearing in the pattern tree: a match is only possible if EVERY one of them
/// has a ground occurrence (the matcher walks the whole pattern structurally,
/// and a missing nested symbol makes the match fail just as surely as a missing
/// top symbol).
#[cfg(test)]
fn collect_pattern_required_symbols(pattern: &EMatchPattern, out: &mut HashSet<String>) {
    out.insert(pattern.symbol.name().to_string());
    for arg in &pattern.args {
        if let EMatchArg::Nested(nested) = arg {
            collect_pattern_required_symbols(nested, out);
        }
    }
}

/// Test-only diagnostic: decide whether a *triggered* universal quantifier has
/// no possible trigger instantiation against the ground terms in `assertions`.
///
/// A multi-trigger GROUP can fire only if EVERY pattern in the group can match
/// some ground term, and a pattern `S(..)` can only match a ground term whose
/// head (or, for nested sub-patterns, some reachable ground head) is `S`. Hence
/// a group is *dead* if any required UNINTERPRETED symbol of any of its patterns
/// is absent from the ground term index. The quantifier is *vacuously
/// E-match-complete* iff it has at least one trigger group and EVERY group is
/// dead.
///
/// This is not a semantic SAT predicate. A dead trigger proves only that the
/// trigger-based engine emits no instance; the quantified body may still be
/// contradictory at every binder value. INTERPRETED/theory symbols (`+`,
/// `select`, `bvadd`, `seq.nth`, …) are deliberately excluded even from this
/// structural diagnostic because matching can coincide through theory
/// reasoning. A quantifier with no user trigger returns `false`.
#[cfg(test)]
pub(crate) fn quantifier_has_no_possible_trigger_match(
    terms: &TermStore,
    quantifier: TermId,
    assertions: &[TermId],
) -> bool {
    // Only triggered foralls are in scope. An untriggered forall is handled by
    // CEGQI/enumeration and must not be classified as vacuous here.
    let has_user_triggers = matches!(
        terms.get(quantifier),
        TermData::Forall(_, _, triggers) if !triggers.is_empty()
    );
    if !has_user_triggers {
        return false;
    }

    let extracted = extract_patterns_with_fallback(terms, quantifier);

    // Consider ALL trigger groups the engine could ever try: the
    // user-trigger-derived primary groups AND the auto-synthesized fallback
    // groups (the engine runs fallback when the primary groups instantiated
    // nothing). The quantifier can be instantiated iff at least one of these
    // groups can fire, so it is vacuously dead only when EVERY group — primary
    // and fallback — is dead. If there are no groups at all (e.g. the body has
    // no usable pattern), we cannot certify vacuity and return false.
    if extracted.primary.is_empty() && extracted.fallback.is_empty() {
        return false;
    }

    let index = TermIndex::new(terms, assertions);

    // A group is dead if ANY of its patterns has a required UNINTERPRETED symbol
    // with no ground occurrence (the matcher walks the whole pattern
    // structurally; a missing symbol anywhere makes the match impossible).
    //
    // SOUNDNESS (P0 wrong-sat, patterned-forall): the death test — and the
    // caller's "extend the model by interpreting the never-grounded symbol
    // freely" vacuity argument — is valid ONLY for UNINTERPRETED symbols. An
    // INTERPRETED/theory symbol in the pattern (e.g. `+` in `f(+ x 1)`) has a
    // FIXED meaning and cannot be "reinterpreted freely": the trigger term
    // `(+ x 1)` semantically ranges over the whole integer domain, so it can
    // coincide with an existing ground argument (`x := -1` gives `f 0`) even
    // though `+` never occurs in a ground term. Counting `+`'s absence as
    // proof of vacuity wrongly certifies `forall x. f(x+1) >= 0 ∧ f(0) = -1`
    // as SAT (truth: UNSAT). We therefore EXCLUDE builtin/theory symbols from
    // the required-symbol death test: only a genuinely uninterpreted symbol
    // with no ground occurrence proves the pattern can never fire. This only
    // ever WEAKENS vacuity (a pattern whose sole missing symbol is interpreted
    // is now NOT certified dead), routing the SAT through the normal
    // MBQI/CEGQI counter-check — fail-closed, never a new UNSAT.
    let group_is_dead = |group: &pattern::TriggerGroup| -> bool {
        group.patterns.iter().any(|pattern| {
            let mut required: HashSet<String> = HashSet::default();
            collect_pattern_required_symbols(pattern, &mut required);
            required.iter().any(|sym| {
                !crate::features::is_builtin_symbol_name(sym) && index.get_by_symbol(sym).is_empty()
            })
        })
    };

    let all_dead = extracted.primary.iter().all(&group_is_dead)
        && extracted.fallback.iter().all(&group_is_dead);
    all_dead
}

/// (#auflia-disjunct-forall-false-unsat) Collect, in deterministic order, the universal
/// quantifiers ENTAILED as NNF CONJUNCTS of `term` under the given `positive`
/// polarity. This is the CANONICAL entailment predicate for every lane that
/// conjoins a ground instance `body[t/x]` into the assertion set as a
/// TOP-LEVEL CONJUNCT.
///
/// # Why every instantiation lane must consult it
///
/// `∀x. body ⊨ body[t/x]` (universal instantiation) is a consequence of the
/// QUANTIFIER, not of the PROBLEM. It licenses conjoining `body[t/x]` only when
/// the problem entails `∀x. body` itself. When the `forall` sits in a
/// disjunctive position — `(or c (forall x. p x))`, an `ite` branch, a positive
/// `=>` conclusion — the problem entails only the enclosing disjunction, and
/// conjoining an instance FABRICATES a constraint: a genuinely-SAT problem can
/// be turned UNSAT. That is exactly the `#auflia-disjunct-forall-false-unsat`
/// defect (six 20170829-Rodin files answered `unsat` against a declared and
/// triply-oracle-confirmed `sat`, with `conflicts=0 decisions=0` — the whole
/// refutation came from conjoined instances, not from search).
///
/// The walk descends ONLY through connectives that preserve conjunct-hood:
///  * positive `and` (each arg is entailed),
///  * negative `or`  (`¬(a ∨ b) ≡ ¬a ∧ ¬b`),
///  * negative `=>`  (`¬(a₁ ⇒ … ⇒ aₙ) ≡ a₁ ∧ … ∧ aₙ₋₁ ∧ ¬aₙ`, right-assoc),
///  * `not` (flips polarity).
///
/// It collects a positive `Forall` directly, and a negative `Exists` as its
/// minted NNF-dual `forall x. ¬body` — the SAME construction (and therefore the
/// same hash-consed `TermId`) as [`collect_quantifiers`]'s `Not(Exists)` arm, so
/// membership tests against a `collect_quantifiers` list line up exactly.
///
/// It STOPS at every other position (positive `or`/`=>`, both-polarity `ite`,
/// `xor`, `=`, quantifier bodies, `let`, uninterpreted apps): a quantifier
/// reachable only past one of those is NOT entailed. Dropping a candidate is
/// always FAIL-SAFE for the UNSAT direction — an instantiation lane that
/// instantiates fewer quantifiers only weakens the conjunction, so it can lose
/// a refutation (sound `unknown`) but never manufacture one.
///
/// Strictly WIDER than [`collect_unconditional_foralls`] (which is `and`-only
/// and is the narrower provenance filter for proof/support-axiom tagging) and
/// strictly NARROWER than [`collect_quantifiers`] (which flattens through
/// `or`/`ite` with no polarity at all). Do not substitute one for another.
pub(crate) fn collect_entailed_foralls(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
    out: &mut Vec<TermId>,
) {
    collect_entailed_foralls_with_units(terms, term, positive, &UnitFacts::default(), out);
}

/// Top-level unit facts of an assertion list: atom -> its asserted truth value.
///
/// A bare atom assertion is a FACT, and the entailment test has to be taken
/// modulo those facts rather than read off the syntax tree alone. This is the
/// same `#unit-conjunctive` refinement `forall_ids_in_conjunctive_position`
/// already applies for the MBQI gate: `(=> ext_eq_0 (forall i. B i))` puts its
/// `forall` in a syntactically DISJUNCTIVE position, yet with `(assert
/// ext_eq_0)` also present the universal is an outright top-level consequence
/// and its instances are sound ground facts. Reading that shape syntactically
/// discarded a genuine UNSAT once already (#7956); it also loses the
/// `∀x. q(x) ⇒ ∀x. p(x)` + `q(0)` + `¬p(1)` refutation.
///
/// Unit-simplifying first is sound (a unit assertion is unconditionally true)
/// and strictly more accurate: it only ever RECOGNISES universals that really
/// are consequences, never admits one that is not.
#[derive(Default)]
pub(crate) struct UnitFacts {
    values: HashMap<TermId, bool>,
}

impl UnitFacts {
    /// Collect the top-level unit facts of `assertions`.
    pub(crate) fn from_assertions(terms: &TermStore, assertions: &[TermId]) -> Self {
        let mut values: HashMap<TermId, bool> = HashMap::default();
        for &a in assertions {
            match terms.get(a) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    if is_unit_atom(terms, inner) {
                        values.insert(inner, false);
                    }
                }
                _ => {
                    if is_unit_atom(terms, a) {
                        values.insert(a, true);
                    }
                }
            }
        }
        Self { values }
    }

    /// Truth of `t` under the units, if determined. Handles a negated atom by
    /// flipping its atom's unit value.
    fn value(&self, terms: &TermStore, t: TermId) -> Option<bool> {
        if let Some(&v) = self.values.get(&t) {
            return Some(v);
        }
        if let TermData::Not(inner) = terms.get(t) {
            if let Some(&v) = self.values.get(inner) {
                return Some(!v);
            }
        }
        None
    }

    fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}

/// Is `t` an atom that a bare assertion of it pins as a unit fact? (Mirrors
/// `result_mapping::is_unit_atom`.)
fn is_unit_atom(terms: &TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Forall(..) | TermData::Exists(..) | TermData::Not(..) => false,
        TermData::App(ay_core::Symbol::Named(name), _) => {
            !matches!(name.as_str(), "and" | "or" | "=>" | "not" | "ite" | "xor")
        }
        _ => true,
    }
}

/// [`collect_entailed_foralls`], taken modulo the top-level unit facts in
/// `units` (see [`UnitFacts`]). With empty units this is exactly the syntactic
/// walk.
pub(crate) fn collect_entailed_foralls_with_units(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
    units: &UnitFacts,
    out: &mut Vec<TermId>,
) {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Forall(..) => {
                if positive {
                    out.push(term);
                }
                // Negative forall = existential: not entailed as a universal.
            }
            TermData::Exists(vars, body, triggers) => {
                if !positive {
                    // NNF: NOT(exists x. phi) is the entailed universal
                    // forall x. NOT(phi).
                    let neg_body = terms.mk_not(body);
                    let converted = terms.mk_forall_with_triggers(vars, neg_body, triggers);
                    terms.copy_quantifier_metadata(term, converted);
                    out.push(converted);
                }
            }
            TermData::Not(inner) => {
                collect_entailed_foralls_with_units(terms, inner, !positive, units, out);
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                if (positive && name == "and") || (!positive && name == "or") {
                    for arg in args {
                        collect_entailed_foralls_with_units(terms, arg, positive, units, out);
                    }
                } else if !positive && name == "=>" && !args.is_empty() {
                    // ¬(a₁ ⇒ … ⇒ aₙ) ≡ a₁ ∧ … ∧ aₙ₋₁ ∧ ¬aₙ (right-assoc n-ary).
                    let last = args.len() - 1;
                    for (i, arg) in args.into_iter().enumerate() {
                        collect_entailed_foralls_with_units(terms, arg, i < last, units, out);
                    }
                } else if !units.is_empty() && positive && name == "=>" && args.len() == 2 {
                    // (#unit-conjunctive) `(=> a b)` with `a` a unit FACT makes
                    // `b` a top-level consequence. Sound: `a` is unconditionally
                    // true, so the implication reduces to `b`.
                    if units.value(terms, args[0]) == Some(true) {
                        collect_entailed_foralls_with_units(terms, args[1], positive, units, out);
                    }
                } else if !units.is_empty() && positive && name == "or" {
                    // (#unit-conjunctive) Unit propagation through a positive
                    // `or`: when no disjunct is already TRUE and every disjunct
                    // but one is FALSIFIED by a unit fact, the survivor is a
                    // top-level consequence.
                    if !args.iter().any(|&x| units.value(terms, x) == Some(true)) {
                        let live: Vec<TermId> = args
                            .iter()
                            .copied()
                            .filter(|&x| units.value(terms, x) != Some(false))
                            .collect();
                        if live.len() == 1 {
                            collect_entailed_foralls_with_units(
                                terms, live[0], positive, units, out,
                            );
                        }
                    }
                }
                // Every other App (positive or / =>, xor, =, uninterpreted, …):
                // STOP — nothing below is an entailed conjunct.
            }
            // ite (either polarity), let, atoms, leaves: STOP (fail-safe).
            _ => {}
        }
    }) // stacker::maybe_grow
}

/// The entailed-universal set of a whole assertion list, as a membership index.
/// Every assertion root is walked at positive polarity (asserted = true), taken
/// modulo the list's own top-level unit facts.
pub(crate) fn entailed_forall_set(terms: &mut TermStore, assertions: &[TermId]) -> HashSet<TermId> {
    let units = UnitFacts::from_assertions(terms, assertions);
    let mut acc: Vec<TermId> = Vec::new();
    for &assertion in assertions {
        collect_entailed_foralls_with_units(terms, assertion, true, &units, &mut acc);
    }
    acc.into_iter().collect()
}

pub(crate) fn collect_quantifiers(terms: &mut TermStore, term: TermId, out: &mut Vec<TermId>) {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term).clone() {
            // An `Exists` IS surfaced here, and that is deliberate — do not
            // "fix" the #auflia-exists-eq-false-unsat wrong-`unsat` at this site
            // (#auflia-exists-eq-collector-must-still-surface).
            //
            // Surfacing is not instantiation. The unsound step was the E-matching
            // loop DESTRUCTURING an `Exists` as an instantiation target; that is
            // refused at the single point where it happens, in
            // `perform_ematching_with_generations` (`TermData::Exists(..) =>
            // continue`). Everything downstream of THIS function needs the
            // existential to keep flowing through:
            //
            //   * it lands in `uninstantiated_quantifiers`, setting
            //     `has_uninstantiated`, which is one of the conjuncts blocking
            //     the `full_ematching_coverage` SAT certificate;
            //   * `quantifier_loop::mod.rs` recomputes this same list to derive
            //     `ematching_has_exists`; and
            //   * `setup_cegqi_for_unhandled` iterates it, so a positive-position
            //     existential is routed to CEGQI, or else recorded as unhandled.
            //
            // Dropping the `Exists` arm here silences all three at once: the
            // existential becomes invisible rather than unhandled, and the ground
            // solve's `sat` can then be returned as authoritative with the
            // existential never discharged. That trades a wrong `unsat` for a
            // wrong `sat`, which is the worse direction — the wrong `unsat` was
            // already closed at the instantiation site.
            TermData::Forall(..) | TermData::Exists(..) => {
                out.push(term);
            }
            TermData::Not(inner) => {
                match terms.get(inner).clone() {
                    // NNF: NOT(exists x. phi) → forall x. NOT(phi)
                    TermData::Exists(vars, body, triggers) => {
                        let neg_body = terms.mk_not(body);
                        let converted = terms.mk_forall_with_triggers(vars, neg_body, triggers);
                        terms.copy_quantifier_metadata(inner, converted);
                        out.push(converted);
                    }
                    // NNF: NOT(forall x. phi) → exists x. NOT(phi)
                    TermData::Forall(vars, body, triggers) => {
                        let neg_body = terms.mk_not(body);
                        let converted = terms.mk_exists_with_triggers(vars, neg_body, triggers);
                        terms.copy_quantifier_metadata(inner, converted);
                        out.push(converted);
                    }
                    _ => collect_quantifiers(terms, inner, out),
                }
            }
            TermData::App(_, args) => {
                for arg in args {
                    collect_quantifiers(terms, arg, out);
                }
            }
            TermData::Ite(c, t, e) => {
                collect_quantifiers(terms, c, out);
                collect_quantifiers(terms, t, out);
                collect_quantifiers(terms, e, out);
            }
            TermData::Let(bindings, body) => {
                let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                for val in vals {
                    collect_quantifiers(terms, val, out);
                }
                collect_quantifiers(terms, body, out);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // Future TermData variants: skip (no quantifiers to collect).
            _ => {}
        }
    }) // stacker::maybe_grow
}

/// Collect the Foralls that are UNCONDITIONALLY asserted by `term` — i.e. the
/// top-level conjuncts of the asserted formula. A Forall reached this way is
/// entailed by the problem (`∀x. body` is asserted), so every ground instance
/// `body[t/x]` is true in EVERY model (universal instantiation). This is the
/// SOUND provenance filter that lets the fail-closed conflict-verification gate
/// re-supply the e-matched instances an isolated combiner dropped, without ever
/// laundering a spurious conflict.
///
/// # Soundness — the walk is deliberately STRICT
///
/// It recurses ONLY through:
///  * the assertion root itself, and
///  * `App` whose head symbol is `and` (conjunction).
///
/// It STOPS (does not descend) at `or`, `ite`, `=>`, `not`, and any other
/// `App` — a Forall reached under a disjunction/conditional is NOT a top-level
/// conjunct, so `∀x. body` is not entailed (only the enclosing disjunction is)
/// and its instances could turn a genuinely-SAT set UNSAT. Only `TermData::Forall`
/// is ever inserted, so Exists are never surfaced.
///
/// This is intentionally NARROWER than [`collect_quantifiers`], which flattens
/// through `or`/`ite` args WITHOUT polarity tracking and would surface
/// non-entailed Foralls; do NOT substitute one for the other.
pub(crate) fn collect_unconditional_foralls(
    terms: &TermStore,
    term: TermId,
    out: &mut HashSet<TermId>,
) {
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term).clone() {
            TermData::Forall(..) => {
                // A top-level conjunct Forall: unconditionally asserted.
                out.insert(term);
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                // Conjunction preserves top-level-conjunct-hood: recurse.
                for arg in args {
                    collect_unconditional_foralls(terms, arg, out);
                }
            }
            // STOP at every other connective (or / ite / => / not / other App),
            // every Exists, and all atoms/leaves: a Forall reachable only past
            // one of these is NOT unconditionally asserted.
            _ => {}
        }
    }) // stacker::maybe_grow
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
