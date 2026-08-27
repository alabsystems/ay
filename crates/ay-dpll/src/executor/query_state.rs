// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-scoped provenance and bounded-work state shared by executor phases.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermEntryStamp;
use ay_core::{TermId, TermStore};

/// Lifetime entry counters for check-sat pre-passes that sit behind a mode
/// guard (#prepass-reachability).
///
/// A pre-pass guarded on a predicate that is unconditionally FALSE on the
/// public path is DEAD, not opted out — and it is dead SILENTLY: every test
/// still passes the moment the pass has a fail-closed degradation, because the
/// degradation is exactly what a never-run pass produces. That failure mode has
/// already cost this codebase twelve passes (see the doc comment on
/// [`super::Executor::produce_proofs_enabled`] and the eleventh/twelfth sites in
/// `check_sat.rs`), and no verdict-level assertion can catch it: the verdict is
/// identical either way.
///
/// The counters below make reachability itself observable, so a regression test
/// can assert that a pre-pass really executed on the lane that owns it. They are
/// incremented only at the pre-pass entry point, are never read by solver logic,
/// and never influence a verdict.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct PrepassReachability {
    /// Times the deep-QE pre-pass site was reached with its APPLICABILITY
    /// condition (quantified assertions present) satisfied. Everything that can
    /// keep `deep_qe_entered` below this is a mode guard.
    pub(crate) deep_qe_applicable: u64,
    /// Times the deep-QE pre-pass actually ran
    /// (`crate::executor::qe_prepass::deep_qe`).
    pub(crate) deep_qe_entered: u64,
    /// Times the INTERNAL proof tracker was recording at the deep-QE site, i.e.
    /// `produce_proofs_enabled()` was true there. Sampled in situ so the
    /// regression test can pin the trap as a measured fact rather than as a
    /// claim about `begin_public_solve` made from somewhere else.
    pub(crate) deep_qe_internal_tracker_on: u64,
    /// Times `deep_qe_unknown_retry` cleared every guard AND its probe found a
    /// real rewrite, so an `Unknown` was re-solved with the pre-pass armed. This
    /// is the attribution counter: a behaviour change on a query with this at
    /// zero did not come from the deep-QE lane.
    pub(crate) deep_qe_unknown_retries: u64,
    /// Times the #qe-alternation-route recognizer ACCEPTED the problem (pure
    /// arithmetic, quantified, no UF / arrays / BV / nonlinear) at the pre-pass
    /// site, i.e. the route was applicable.
    pub(crate) qe_route_applicable: u64,
    /// Times the #qe-alternation-route actually adopted a fully quantifier-free
    /// residue, so `has_quantified_assertions` was recomputed to false and the
    /// ground lane owned the rest of the solve. The gap to
    /// `qe_route_applicable` is the eliminators' fail-closed refusal rate.
    pub(crate) qe_route_grounded: u64,
}

/// Provenance of one finite-domain quantifier expansion that replaced a
/// top-level `forall` assertion with its ground instance conjunction
/// (#quant-expansion-proof).
///
/// Recorded by `expand_finite_domains` and kept in sync by the later
/// in-place assertion rewrites of the quantifier lane (strict-int
/// tightening), so at proof-export time `expanded` still equals the
/// solver-visible assertion the exported `assume` carries. The trust
/// surgery matches an unmatched `assume` against `expanded`, then derives
/// each consumed conjunct from `original` (the genuine problem premise)
/// with `forall_inst` + guard-discharge steps, using `instances` to look
/// up the binder-value tuple that produced the conjunct.
#[derive(Debug, Clone)]
pub(crate) struct QuantExpansionRecord {
    /// The original assertion — the `forall` term itself.
    pub(crate) original: TermId,
    /// Position of the replaced assertion on the assertion stack at
    /// expansion time (aligned with `assertions_parsed()` for the
    /// non-flattened prefix; the surgery re-verifies the surface shape).
    pub(crate) assertion_index: usize,
    /// The current ground replacement conjunction (tracks in-place rewrites).
    pub(crate) expanded: TermId,
    /// Per enumerated instantiation: binder values (in binder order) and the
    /// folded instance term as merged into `expanded` (kept in sync with the
    /// same rewrites).
    pub(crate) instances: Vec<(Vec<TermId>, TermId)>,
}

/// Authenticated proof provenance for one direct E-matching instance.
///
/// Unlike [`QuantExpansionRecord`], E-matching does not replace the authored
/// `forall` on the assertion stack. The record is retained only after the
/// proof tracker has independently replayed the exact substitution from a
/// direct problem assertion. Trust-leaf surgery may then use the same
/// source/binding/instance triple to reconstruct a checked `forall_inst`
/// consequence instead of exporting a `Generic` lemma.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EmatchingProofRecord {
    /// Position of the direct authored `forall` in the immutable assertion
    /// stack (and therefore in `assertions_parsed()`).
    pub(crate) assertion_index: usize,
    /// Canonical source term seen by the E-matcher. Retained so repair can
    /// match a folded `not(forall)` leaf before rebuilding the source term.
    pub(crate) quantifier: TermId,
    /// Positional binder values independently checked by the proof tracker.
    pub(crate) binding: Vec<TermId>,
    /// Exact ground body produced by simultaneous substitution.
    pub(crate) instance: TermId,
}

/// Provenance for one in-place single-binder Skolemization
/// (#skolem-unit-authority).
///
/// Captured only for a TOP-LEVEL authored `exists x. B` (positive) or
/// `not (forall x. B)` (negative) assertion whose fresh witness is a plain
/// Skolem constant. `instance` is the exact raw substitution `B[x := witness]`
/// as minted by the Skolemizer; `asserted` is the term actually placed on the
/// assertion stack (Boolean folding may differ from the raw form). The
/// checked-SAT-refutation sidecar seals each record behind an epoch/stamp
/// token and independently replays the substitution before use.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SkolemInstanceRecord {
    /// The authored assertion term (`exists ...` or `not (forall ...)`).
    pub(crate) source: TermId,
    /// The quantifier itself (equals `source` in the positive case).
    pub(crate) quantified: TermId,
    /// Fresh Skolem constant minted for the single binder.
    pub(crate) witness: TermId,
    /// Exact raw substituted body `B[x := witness]`.
    pub(crate) instance: TermId,
    /// Final term written to the assertion stack.
    pub(crate) asserted: TermId,
    /// `true` for `exists`, `false` for `not (forall ...)`.
    pub(crate) positive: bool,
}

/// Provenance for one single-binder Skolemization ANYWHERE in an authored
/// assertion, including existentials nested under Boolean connectives
/// (#skolem-witness-sat).
///
/// Unlike [`SkolemInstanceRecord`] — whose positive arm is restricted to a
/// TOP-LEVEL authored `exists` because the checked-SAT-refutation sidecar
/// derives the whole asserted unit from `source` — this record certifies only
/// the NODE-LOCAL fact "`quantified` was Skolemized with `witness`, and
/// `instance` is the exact raw substitution". Its single consumer is the
/// skolem-witness SAT confirmation arm (`try_skolem_witness_sat_confirmation`),
/// which independently REPLAYS binder shape, witness registry membership,
/// registered `SkolemChoice` identity, and the exact substitution at
/// consumption time before using `instance` in a polarity-sound rewrite. It
/// must never feed the c5 derivation channel: for a nested `quantified`,
/// deriving `source` from the quantifier alone would be unsound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SkolemWitnessRecord {
    /// The quantifier node (`Exists` for positive, `Forall` for the
    /// negated-`forall` shape) as it occurs inside the authored assertion.
    pub(crate) quantified: TermId,
    /// Fresh Skolem constant minted for the single binder.
    pub(crate) witness: TermId,
    /// The Skolemizer's substituted body `B[x := witness]` (NOT negated for
    /// the `Forall` shape). DIAGNOSTIC ONLY: the consuming arm recomputes the
    /// raw substitution itself at consumption and never trusts this field
    /// (the Skolemizer substitutes with simplification, so the recorded form
    /// can differ syntactically from the exact raw instance).
    pub(crate) instance: TermId,
    /// `true` for a positive `exists`, `false` for a negative `forall`.
    pub(crate) positive: bool,
}

/// Provenance for one BV-MBQI boundary instance that constant-folded to a
/// definite `false` and was pushed as a refuting assertion
/// (#bv-mbqi-false-instance-authority, P3b).
///
/// Recorded at the exact push site in `try_bv_mbqi_refinement`: the model-less
/// refute-only mode pushes a ground boundary instance whose empty-model
/// constant fold is a definite `false`; downstream preprocessing then folds
/// the pushed assertion to the literal `false` term, and the SAT layer sees an
/// original unit clause `[false]` that no authored term matches. `instance` is
/// the exact RAW simultaneous substitution `body[binders := values]` (minted
/// with `subst_vars_exact_qf`, the same non-simplifying form the strict
/// `forall_inst` validator replays); `asserted` is the `false` fold target and
/// is the fragment-map KEY. The checked-SAT-refutation sidecar seals each
/// record behind an epoch/stamp token, independently replays the substitution
/// AND the model-free fold claim before use; the emitted chain discharges the
/// fold through a strict `BvLiaTautology` bridge the checker re-proves from
/// scratch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BvMbqiFalseInstanceRecord {
    /// The source `forall` term (must be authored-admissible at emission).
    pub(crate) quantifier: TermId,
    /// Positional binder values (boundary candidates), in binder order.
    pub(crate) values: Vec<TermId>,
    /// Exact raw substituted body `body[binders := values]`.
    pub(crate) instance: TermId,
    /// Folded term actually pushed onto the assertion stack (the literal
    /// `false` term for every record this campaign admits).
    pub(crate) asserted: TermId,
}

/// Provenance for one qpf premise-forced instance pushed for the
/// refutation-driven re-solve (#ppp-c7, L2).
///
/// Recorded at the exact push site in `premise_forced_binder_refutation`
/// AFTER the disposable checked ground refutation of the substituted body
/// succeeded: the lane then pushes the simplified instance (`asserted` =
/// `body[binders := literals]` through the simplifying substituter) and
/// re-solves the PUBLIC query so its own trace can mint the OUTER
/// checked-SAT-refutation sidecar the quantified-UNSAT artifact firewall
/// demands. `instance` is the exact RAW simultaneous substitution (minted
/// with `subst_vars_exact_qf`, the form the strict `forall_inst` validator
/// replays). The sidecar seals each record behind an epoch/stamp token that
/// independently replays the substitution and re-verifies, per disjunct,
/// the model-free `false` fold of every eliminated premise disjunct; the
/// emitted chain re-derives every elimination through zero-variable
/// exhaustively-evaluated lemmas the checker re-decides from scratch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct QpfPremiseForcedInstanceRecord {
    /// The source `forall` term (must be authored-admissible at emission).
    pub(crate) quantifier: TermId,
    /// Positional binder literals (premise-pinned values), in binder order.
    pub(crate) values: Vec<TermId>,
    /// Exact raw substituted body `body[binders := values]`.
    pub(crate) instance: TermId,
    /// Simplified term actually pushed onto the assertion stack.
    pub(crate) asserted: TermId,
}

/// Producer hint for the #dt-context-derivation fragment channel: a solver-
/// injected clause that is NOT a standalone theory tautology but IS entailed
/// by the recorded `premises` (asserted top-level facts). The record grants
/// no authority by itself: sealing independently re-derives the entailment
/// (the widened clause `clause ∨ ¬premises` must pass the bounded ground
/// refuter), and the fragment lane re-derives it AGAIN at consumption while
/// discharging every premise as an authored assumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DtContextConflictRecord {
    /// The emitted clause's literal terms, in emission order.
    pub(crate) clause: Vec<TermId>,
    /// Asserted premise terms that make the clause entailed.
    pub(crate) premises: Vec<TermId>,
}

/// Deduplicated, capped store for [`DtContextConflictRecord`] producer hints
/// (#dt-context-derivation). Theory propagations re-mint across restarts by
/// the thousands; normalized-clause keying retains a bounded set of distinct
/// premise alternatives, so duplicate traffic cannot crowd out conflict records.
#[derive(Debug, Clone, Default)]
pub(crate) struct DtContextConflictSink {
    pub(crate) records: Vec<DtContextConflictRecord>,
    keys: ay_core::kani_compat::DetHashMap<Vec<TermId>, u8>,
}

impl DtContextConflictSink {
    const MAX_RECORDS: usize = 16384;
    const MAX_PREMISES: usize = 32;
    /// Alternatives kept per normalized clause. Different emitters justify
    /// the same fact through different premise sets (a rewrite-time hint vs
    /// a mid-solve reason walk); consumption tries each until one
    /// discharges, so a single undischargeable early hint cannot shadow a
    /// later usable one.
    const MAX_PER_KEY: u8 = 6;

    /// Capped, per-key-bounded record; degenerate hints are dropped (a
    /// missing hint can only decline an authentication, never mint one).
    pub(crate) fn record(&mut self, clause: Vec<TermId>, premises: Vec<TermId>) {
        if clause.is_empty()
            || premises.is_empty()
            || premises.len() > Self::MAX_PREMISES
            || self.records.len() >= Self::MAX_RECORDS
        {
            return;
        }
        let mut key = clause.clone();
        key.sort_unstable();
        key.dedup();
        let slot = self.keys.entry(key).or_insert(0);
        if *slot >= Self::MAX_PER_KEY {
            return;
        }
        *slot += 1;
        self.records
            .push(DtContextConflictRecord { clause, premises });
    }

    pub(crate) fn is_full(&self) -> bool {
        self.records.len() >= Self::MAX_RECORDS
    }

    pub(crate) fn clear(&mut self) {
        self.records.clear();
        self.keys.clear();
    }
}

/// The clique behind a finite-enum pigeonhole refutation, with per-pair source
/// provenance so the proof layer can emit real `Assume` steps.
#[derive(Debug, Clone)]
pub(crate) struct FiniteEnumPigeonholeWitness {
    /// Constructor count of the sort (its exact carrier size).
    pub(crate) k: usize,
    /// `k + 1` pairwise-distinct terms of that sort.
    pub(crate) members: Vec<TermId>,
    /// Ordered member pair -> the authored assertion that supplied it.
    pub(crate) edge_sources: HashMap<(TermId, TermId), TermId>,
}

/// Query-cumulative budget and idempotence ledger for exact finite-array
/// closure.
///
/// The remaining counters are replenished only at an *external* decision
/// boundary. Internal retries, DT fallbacks, core-minimization probes, and
/// route-local re-entry therefore share one deterministic allocation envelope.
/// The axiom maps survive between public queries only as an idempotence index;
/// a map entry is authoritative solely while its axiom is still present in the
/// active assertion stack (the generator checks that before reusing it).
#[derive(Debug)]
pub(crate) struct FiniteArrayExpansionLedger {
    pub(crate) remaining_index_points: usize,
    pub(crate) remaining_value_cells: usize,
    /// Remaining distinct term nodes that finite-array discovery may inspect.
    /// This is query-cumulative so retries cannot turn a bounded scan into
    /// unbounded aggregate work.
    pub(crate) remaining_scan_nodes: usize,
    /// Remaining outgoing term-graph edges that discovery may enqueue.
    pub(crate) remaining_scan_edges: usize,
    /// Remaining equality/select candidates admitted to bounded worklists.
    pub(crate) remaining_candidates: usize,
    /// Query-cumulative exact term births already charged to the scanner.
    pub(crate) scanned_nodes: HashSet<(TermId, TermEntryStamp)>,
    /// In insertion order, every finite-array candidate discovered during this
    /// external query. Entries are authenticated by the exact term birth stamp
    /// and the vector is bounded by `MAX_CANDIDATES` through the admission
    /// ledger. Replaying this compact index lets later route passes avoid
    /// walking immutable term DAGs again.
    pub(crate) discovered_candidates: Vec<(TermId, TermEntryStamp)>,
    /// Test-only count of actual TermData/sort inspections, distinct from the
    /// accounting counters so regressions can prove a replay did not walk the
    /// DAG while merely declining to recharge it.
    #[cfg(test)]
    pub(crate) discovery_term_inspections: usize,
    pub(crate) admitted_equalities: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) admitted_selects: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) equality_axioms: HashMap<TermId, FiniteArrayCachedAxiom>,
    pub(crate) select_axioms: HashMap<TermId, FiniteArrayCachedAxiom>,
    pub(crate) covered_equalities: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) covered_selects: HashSet<(TermId, TermEntryStamp)>,
    /// Selects whose exact finite-domain expansion simplified to the select
    /// itself. Unlike `covered_selects`, these need no active cached axiom, but
    /// their stamped identity still makes reuse safe across speculative slot
    /// recycling.
    pub(crate) trivially_covered_selects: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) deferred_equalities: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) deferred_selects: HashSet<(TermId, TermEntryStamp)>,
    pub(crate) candidate_scan_truncated: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FiniteArrayCachedAxiom {
    pub(crate) candidate_stamp: TermEntryStamp,
    pub(crate) axiom: TermId,
    pub(crate) axiom_stamp: TermEntryStamp,
}

impl FiniteArrayExpansionLedger {
    pub(crate) const MAX_INDEX_POINTS: usize = 4_096;
    pub(crate) const MAX_VALUE_CELLS: usize = 65_536;
    pub(crate) const MAX_SCAN_NODES: usize = 65_536;
    pub(crate) const MAX_SCAN_EDGES: usize = 262_144;
    pub(crate) const MAX_CANDIDATES: usize = 4_096;

    fn new() -> Self {
        Self {
            remaining_index_points: Self::MAX_INDEX_POINTS,
            remaining_value_cells: Self::MAX_VALUE_CELLS,
            remaining_scan_nodes: Self::MAX_SCAN_NODES,
            remaining_scan_edges: Self::MAX_SCAN_EDGES,
            remaining_candidates: Self::MAX_CANDIDATES,
            scanned_nodes: HashSet::default(),
            discovered_candidates: Vec::new(),
            #[cfg(test)]
            discovery_term_inspections: 0,
            admitted_equalities: HashSet::default(),
            admitted_selects: HashSet::default(),
            equality_axioms: HashMap::default(),
            select_axioms: HashMap::default(),
            covered_equalities: HashSet::default(),
            covered_selects: HashSet::default(),
            trivially_covered_selects: HashSet::default(),
            deferred_equalities: HashSet::default(),
            deferred_selects: HashSet::default(),
            candidate_scan_truncated: false,
        }
    }

    /// Replenish work allowance while retaining only cross-query axiom maps.
    pub(crate) fn begin_external_query(&mut self) {
        self.remaining_index_points = Self::MAX_INDEX_POINTS;
        self.remaining_value_cells = Self::MAX_VALUE_CELLS;
        self.remaining_scan_nodes = Self::MAX_SCAN_NODES;
        self.remaining_scan_edges = Self::MAX_SCAN_EDGES;
        self.remaining_candidates = Self::MAX_CANDIDATES;
        self.scanned_nodes.clear();
        self.discovered_candidates.clear();
        #[cfg(test)]
        {
            self.discovery_term_inspections = 0;
        }
        self.admitted_equalities.clear();
        self.admitted_selects.clear();
        self.covered_equalities.clear();
        self.covered_selects.clear();
        self.trivially_covered_selects.clear();
        self.deferred_equalities.clear();
        self.deferred_selects.clear();
        self.candidate_scan_truncated = false;
    }

    /// Retain only cache entries whose exact candidate and axiom births still
    /// exist and whose axiom is active in the caller's current assertion view.
    /// This keeps long push/pop sessions from accumulating dead cache records.
    pub(crate) fn prune_to_active_assertions(&mut self, terms: &TermStore, assertions: &[TermId]) {
        let active: HashSet<TermId> = assertions.iter().copied().collect();
        let mut retain = |candidate: &TermId, cached: &mut FiniteArrayCachedAxiom| {
            terms.entry_stamp(*candidate) == Some(cached.candidate_stamp)
                && terms.entry_stamp(cached.axiom) == Some(cached.axiom_stamp)
                && active.contains(&cached.axiom)
        };
        self.equality_axioms.retain(&mut retain);
        self.select_axioms.retain(retain);
    }

    pub(crate) fn is_complete(&self) -> bool {
        !self.candidate_scan_truncated
            && self.deferred_equalities.is_empty()
            && self.deferred_selects.is_empty()
    }
}

impl Default for FiniteArrayExpansionLedger {
    fn default() -> Self {
        Self::new()
    }
}

/// Exact meters for the ground-conflict decomposition arms
/// (#ground-conflict-decomp). `attempted` counts trust lemmas the two new
/// planners inspected, `applied` counts lemmas replaced by a checkable
/// derivation, `declined` counts inspected lemmas the planners refused
/// (shape mismatch, Farkas failure, or budget). Cumulative within one
/// executor; published under `proof.ground_conflict_decomp_*` (`--stats`).
#[derive(Debug, Default)]
pub(crate) struct GroundConflictDecompMeters {
    pub(crate) attempted: std::cell::Cell<u64>,
    pub(crate) applied: std::cell::Cell<u64>,
    pub(crate) declined: std::cell::Cell<u64>,
}
