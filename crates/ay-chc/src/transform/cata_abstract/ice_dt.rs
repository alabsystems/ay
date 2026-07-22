// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Horn-ICE decision-tree learner for the catamorphism-abstracted LIA problem
//! ("CATA v3 ICE-DT lane", CHC-COMP agenda #7).
//!
//! # Why this exists
//!
//! [`super::disj_abstract`] computes the *exact* least fixpoint of the Boolean
//! abstract post over the tag-derived atom set. That is inductive by
//! construction, but it materializes EVERY reachable minterm as an explicit
//! DNF disjunct and enumerates them with per-body-combination AllSAT. On the
//! wider sortedness abstractions (`NMSortTDSorts`, `nat_ISortSorts`) the
//! reachable-minterm set and the AllSAT enumeration blow up past the wall
//! deadline even though a compact disjunctive invariant provably exists.
//!
//! This module learns that invariant by GENERALIZATION instead of enumeration:
//! the Horn-ICE decision-tree algorithm (Garg–Neider–Madhusudan–Roth, POPL'16).
//! It maintains a small set of sampled abstract states (POSITIVE / NEGATIVE /
//! IMPLICATION constraints), learns one information-gain decision tree per
//! predicate that classifies them, and checks the resulting candidate against
//! the abstract Horn clauses with the SMT backend. Each counterexample adds one
//! sample and the trees are re-learned. The tree GENERALIZES across the
//! atom-space, so a handful of samples suffices where the exact fixpoint needs
//! thousands of minterms.
//!
//! # Soundness
//!
//! Candidate generator ONLY — identical discipline to [`super::disj_abstract`]
//! and [`super::affine_houdini`]. The returned [`InvariantModel`] is re-certified
//! by the caller (`adaptive_cata::certify_and_compose_abstract_model`) against
//! EVERY abstract clause with a fresh verifier before any verdict is produced. A
//! wrong or non-inductive tree therefore yields NO verdict — never a wrong Safe.
//! Every loop is bounded (atom cap, sample cap, iteration cap, tree-depth cap,
//! wall deadline) and fails closed to `None`.

use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

use crate::expr::evaluate_expr;
use crate::smt::{PdrExecutorBackend, SmtResult, SmtValue};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, InvariantModel, PredicateId,
    PredicateInterpretation,
};

use super::disj_abstract::{
    build_atoms, build_atoms_profiled, canonical_subst, canonical_var, AtomProfile,
};
use super::ColumnTag;

macro_rules! ice_trace {
    ($($arg:tt)*) => {
        if std::env::var_os("AY_ICE_DT_TRACE").is_some() {
            eprintln!("[ice-dt] {}", format!($($arg)*));
        }
    };
}

/// Per-SMT-query timeout inside the CEGAR loop (LIA, few variables — fast).
/// Overridable via `AY_ICE_DT_QUERY_MS` (LRA-spike instrumentation — the raw
/// Real-TS lane poses far heavier per-query LRA obligations than the LIA cata
/// lane, so the spike harness needs to distinguish a budget miss from a genuine
/// solver `Unknown`).
fn query_timeout() -> Duration {
    match std::env::var("AY_ICE_DT_QUERY_MS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        Some(ms) => Duration::from_millis(ms),
        None => Duration::from_millis(400),
    }
}
/// Hard cap on atoms per predicate (a state is a `u64` bitmask ⇒ must stay ≤64).
/// Default 40 (the tested value for the wired cata lane). Overridable up to the
/// bitmask ceiling via `AY_ICE_DT_MAX_ATOMS` for the raw-LRA guard-harvest lane,
/// where an SSL/handshake program counter alone contributes ~30 equality atoms;
/// the DT's information-gain split picks only the relevant features, so a wider
/// pool costs learner time but not soundness.
fn max_atoms_per_pred() -> usize {
    std::env::var("AY_ICE_DT_MAX_ATOMS")
        .ok()
        .and_then(|v| v.parse().ok())
        .map(|n: usize| n.min(64))
        .unwrap_or(40)
}
/// Hard cap on CEGAR refinement iterations (each adds ≥1 sample).
/// Overridable via `AY_ICE_DT_MAX_ITERS` (raw-LRA lanes with many program-counter
/// states need more refinement rounds than the compact cata lane).
fn max_iters() -> usize {
    std::env::var("AY_ICE_DT_MAX_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(600)
}
/// Hard cap on total sampled points across all predicates.
const MAX_SAMPLES: usize = 20_000;
/// Bail if the positive closure has not grown for this many consecutive
/// refinement rounds (divergence guard — e.g. an unbounded size/min column that
/// keeps generating fresh non-reachable edges). Fail closed to `None`.
/// Overridable via `AY_ICE_DT_STALL_LIMIT`.
fn stall_limit() -> usize {
    std::env::var("AY_ICE_DT_STALL_LIMIT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(60)
}
/// Hard cap on decision-tree depth (bounds the learned DNF size per predicate).
const MAX_TREE_DEPTH: usize = 12;

/// Generalization strategy for the per-predicate candidate invariant.
///
/// The Horn-ICE loop is IDENTICAL for both; only how the sampled points are
/// turned into a candidate formula differs. See [`gen_strategy`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum GenStrategy {
    /// Information-gain decision tree (Garg–Neider–Madhusudan–Roth POPL'16) —
    /// GENERALIZES across the atom space, filling the gaps between sampled
    /// points. Compact, but on a raw multi-variable LRA transition system it
    /// OVER-ADMITS: the tree labels whole regions positive that were never
    /// shown reachable, so the inductiveness check keeps finding transitions
    /// out of over-admitted (non-reachable) bodies — the closure saturates
    /// while implication edges grow +1 per round forever (the s3_srvr_4
    /// divergence). Right for the compact cata-abstracted LIA lane.
    InfoGain,
    /// Union-of-cubes (minimal-positive) generalization — the candidate is the
    /// DISJUNCTION of the sampled positive-closure points' full cubes (each
    /// closure point → the conjunction of every atom at its exact polarity).
    /// This admits EXACTLY the reachable-so-far atom-patterns and NOTHING
    /// between them, so the inductiveness check can only ever pick a body that
    /// is already in the closure ⇒ every rule counterexample GROWS the closure
    /// by its new post-state (bounded by the reachable-pattern count) instead
    /// of spinning on non-reachable bodies. This is the tightest sound
    /// generalization and the standard fix for ICE divergence on transition
    /// systems; it also subsumes reachability-guided cex selection (the
    /// pre-state is always in the closure by construction).
    MinCube,
}

/// Read the generalization strategy from `AY_ICE_DT_GEN`
/// (`mincube` | `infogain`). Defaults to `InfoGain` — the proven, wired cata
/// lane is unchanged unless the env explicitly opts into `mincube`.
fn gen_strategy() -> GenStrategy {
    match std::env::var("AY_ICE_DT_GEN").ok().as_deref() {
        Some("mincube") => GenStrategy::MinCube,
        _ => GenStrategy::InfoGain,
    }
}

/// A sampled abstract state: predicate index + atom-truth bitmask (bit `i` set
/// ⟺ atom `i` of that predicate is TRUE).
type Point = (usize, u64);

/// A sampled abstract state as a (possibly PARTIAL) cube: predicate index +
/// atom-truth `value` + a `care` mask marking which atom bits are DETERMINED.
/// Bit `i` of `care` set ⟺ atom `i`'s truth is fixed to bit `i` of `value`;
/// clear ⟺ that atom is a DON'T-CARE (the counterexample model left it free).
///
/// A fully-determined sample has `care` covering every atom index (equivalent
/// to the old concrete [`Point`]); the info-gain lane only ever projects to
/// [`Cube::concrete`] and so is insensitive to `care`. The `mincube` lane uses
/// `care` to keep the candidate TIGHT where the model pinned an atom and GENERAL
/// where it did not — this is what collapses an unconstrained init (dozens of
/// free real-column atoms) into a single small cube instead of an unbounded
/// enumeration of zero-extended completions (the mincube divergence fix).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Cube {
    pred: usize,
    value: u64,
    care: u64,
}

impl Cube {
    /// The concrete (predicate, atom-bitmask) projection: the zero-extended
    /// `value` verbatim (free atoms already resolved to their zero-extension
    /// truth in `value` at sampling time). This is exactly the old concrete
    /// `Point`, so the info-gain lane's closure/labeling is bit-for-bit
    /// unchanged; only the mincube lane consults `care`.
    fn concrete(&self) -> Point {
        (self.pred, self.value)
    }

    /// Does `self` (as a positive-region cube) COVER every concrete state that
    /// matches `other`? True iff same predicate, `self` cares about a SUBSET of
    /// `other`'s atoms, and the two agree on every atom `self` cares about.
    /// (A more-general cube subsumes a more-specific observation.)
    // The lint suggests `other.value & other.care`, but masking BOTH sides by
    // `self.care` is the point: agreement is only required on the atoms `self`
    // cares about (self.care ⊆ other.care is checked on the line above).
    #[allow(clippy::suspicious_operation_groupings)]
    fn subsumes(&self, other: &Cube) -> bool {
        self.pred == other.pred
            && (self.care & !other.care) == 0
            && (self.value & self.care) == (other.value & self.care)
    }
}

/// One Horn implication constraint harvested from a counterexample.
/// `antecedents` are body cubes; `consequent` is the head cube, or `None`
/// when the clause head is `false` (a query clause — the antecedents may not
/// all be positive simultaneously).
struct Impl {
    antecedents: Vec<Cube>,
    consequent: Option<Cube>,
}

/// A learned decision tree over a predicate's atom features.
enum Dt {
    Leaf(bool),
    /// Split on `atom`: `lo` when the atom is FALSE, `hi` when TRUE.
    Node {
        atom: usize,
        lo: Box<Dt>,
        hi: Box<Dt>,
    },
}

impl Dt {
    /// Collect the root→leaf paths that end in a `true` leaf as DNF conjuncts.
    fn collect_paths(&self, atoms: &[ChcExpr], prefix: &mut Vec<ChcExpr>, out: &mut Vec<ChcExpr>) {
        match self {
            Dt::Leaf(true) => {
                out.push(match prefix.len() {
                    0 => ChcExpr::Bool(true),
                    1 => prefix[0].clone(),
                    _ => ChcExpr::and_all(prefix.clone()),
                });
            }
            Dt::Leaf(false) => {}
            Dt::Node { atom, lo, hi } => {
                prefix.push(ChcExpr::not(atoms[*atom].clone()));
                lo.collect_paths(atoms, prefix, out);
                prefix.pop();
                prefix.push(atoms[*atom].clone());
                hi.collect_paths(atoms, prefix, out);
                prefix.pop();
            }
        }
    }

    fn to_expr(&self, atoms: &[ChcExpr]) -> ChcExpr {
        // Shortcut the trivial trees so the candidate formula stays compact.
        match self {
            Dt::Leaf(true) => return ChcExpr::Bool(true),
            Dt::Leaf(false) => return ChcExpr::Bool(false),
            _ => {}
        }
        let mut out = Vec::new();
        let mut prefix = Vec::new();
        self.collect_paths(atoms, &mut prefix, &mut out);
        match out.len() {
            0 => ChcExpr::Bool(false),
            1 => out.into_iter().next().unwrap(),
            _ => {
                // A path with an empty prefix (root leaf true) short-circuits.
                if out.iter().any(|e| matches!(e, ChcExpr::Bool(true))) {
                    ChcExpr::Bool(true)
                } else {
                    ChcExpr::or_all(out)
                }
            }
        }
    }
}

/// Run the Horn-ICE decision-tree learner.
///
/// Returns a candidate [`InvariantModel`] that is inductive + query-excluding
/// on the sampled counterexamples and re-checked against every abstract clause
/// with the SMT backend before being returned — but NOT trusted: the caller
/// re-certifies it. Returns `None` when the atom lattice cannot separate the
/// samples, the loop bounds are hit, or any SMT query is indeterminate (all
/// fail-closed).
pub(crate) fn solve_abstract_ice_dt(
    problem: &ChcProblem,
    tags: &FxHashMap<PredicateId, Vec<ColumnTag>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    debug_assert!(!problem.has_datatype_sorts());
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }

    // Atom set per predicate (index-aligned with predicate order).
    let mut atoms: Vec<Vec<ChcExpr>> = Vec::with_capacity(preds.len());
    for pred in preds {
        let pred_tags = tags.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
        let a = build_atoms(pred.id, &pred.arg_sorts, pred_tags);
        ice_trace!(
            "pred {} ({}) -> {} atoms",
            pred.id.index(),
            pred.name,
            a.len()
        );
        if a.len() > max_atoms_per_pred() {
            ice_trace!(
                "ABORT: pred {} has {} atoms > cap {}",
                pred.name,
                a.len(),
                max_atoms_per_pred()
            );
            return None;
        }
        atoms.push(a);
    }

    run_ice_dt_core(problem, atoms, deadline)
}

/// [`solve_abstract_ice_dt`] over the compact [`AtomProfile::FlagsOnly`]
/// vocabulary — the additive fallback for the WIDE sortedness family
/// (`BSortSorts` and relatives). The full vocabulary blows past the SMT-latency
/// and ay-dpll-`Unknown` walls on those abstracts (see [`AtomProfile`]); the
/// flag-only projection converts them (MEASURED: `BSortSorts` L-sorted abstract
/// → inductive + re-certified, where the full profile and the exact DNF fixpoint
/// both fail). Same soundness contract: candidate generator only, re-certified by
/// the caller, bounded, fails closed to `None`.
pub(crate) fn solve_abstract_ice_dt_flags_only(
    problem: &ChcProblem,
    tags: &FxHashMap<PredicateId, Vec<ColumnTag>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    debug_assert!(!problem.has_datatype_sorts());
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }
    let mut atoms: Vec<Vec<ChcExpr>> = Vec::with_capacity(preds.len());
    for pred in preds {
        let pred_tags = tags.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
        let a = build_atoms_profiled(pred.id, &pred.arg_sorts, pred_tags, AtomProfile::FlagsOnly);
        ice_trace!(
            "[flags-only] pred {} ({}) -> {} atoms",
            pred.id.index(),
            pred.name,
            a.len()
        );
        if a.len() > max_atoms_per_pred() {
            return None;
        }
        atoms.push(a);
    }
    run_ice_dt_core(problem, atoms, deadline)
}

/// [`solve_abstract_ice_dt`] over the [`AtomProfile::NatSize`] vocabulary — the
/// full tag-derived atoms PLUS `size_i <= size_j` leq-splits. This is the lane
/// for the ELEMENT-FREE nat-peano family (no Int payload ⇒ no Min/Max/Sorted
/// level ⇒ the sorted-level ICE lane never fires): their invariants
/// (`min`/`max`/`leq`/`minus`-clamp laws over Peano sizes) are disjunctions
/// split on a size ordering, which the `Full` unit-difference equalities cannot
/// express (MEASURED: `min`/`max` isaplanner props diverge under `Full`, converge
/// with the leq-splits). Same soundness contract: candidate generator only,
/// re-certified by the caller, bounded, fails closed to `None`.
pub(crate) fn solve_abstract_ice_dt_nat(
    problem: &ChcProblem,
    tags: &FxHashMap<PredicateId, Vec<ColumnTag>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    debug_assert!(!problem.has_datatype_sorts());
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }
    let mut atoms: Vec<Vec<ChcExpr>> = Vec::with_capacity(preds.len());
    for pred in preds {
        let pred_tags = tags.get(&pred.id).map(Vec::as_slice).unwrap_or(&[]);
        let a = build_atoms_profiled(pred.id, &pred.arg_sorts, pred_tags, AtomProfile::NatSize);
        ice_trace!(
            "[nat-leq] pred {} ({}) -> {} atoms",
            pred.id.index(),
            pred.name,
            a.len()
        );
        if a.len() > max_atoms_per_pred() {
            return None;
        }
        atoms.push(a);
    }
    run_ice_dt_core(problem, atoms, deadline)
}

/// Core Horn-ICE decision-tree CEGAR loop over an EXPLICIT per-predicate atom
/// set (`atoms[i]` = atoms of `problem.predicates()[i]`, over that predicate's
/// canonical arg vars). Shared by the cata-tag lane ([`solve_abstract_ice_dt`])
/// and the raw Real/Bool LRA lane ([`solve_lra_ice_dt`]); the ONLY difference
/// between the two is the atom SOURCE. Soundness discipline is identical —
/// candidate generator only, every returned model re-certified by the caller,
/// every loop bounded, fails closed to `None`.
pub(crate) fn run_ice_dt_core(
    problem: &ChcProblem,
    atoms: Vec<Vec<ChcExpr>>,
    deadline: Instant,
) -> Option<InvariantModel> {
    let preds = problem.predicates();
    if preds.is_empty() || atoms.len() != preds.len() {
        return None;
    }
    for a in &atoms {
        if a.len() > max_atoms_per_pred() {
            return None;
        }
    }

    // Partition clauses.
    let mut rule_clauses = Vec::new(); // head is a predicate
    let mut query_clauses = Vec::new(); // head is false
    for clause in problem.clauses() {
        match &clause.head {
            ClauseHead::Predicate(..) => rule_clauses.push(clause),
            ClauseHead::False => query_clauses.push(clause),
        }
    }

    let mut backend = PdrExecutorBackend::new();

    // Sample sets. `pos` holds the fact-clause seed points; `impls` holds the
    // reachability edges (rule cexes) and query goals. Negatives are DERIVED by
    // the labeling, never sampled eagerly.
    let mut pos: Vec<Cube> = Vec::new();
    let mut impls: Vec<Impl> = Vec::new();
    let mut total_samples = 0usize;

    // Current candidate invariant per predicate (index-aligned with `preds`),
    // one formula over that predicate's canonical arg vars. Start every
    // predicate at `false` (least element): fact clauses then seed positives.
    // The formula is (re)built each round by [`learn_invariants`] under the
    // active [`GenStrategy`].
    let strategy = gen_strategy();
    ice_trace!("generalization strategy = {:?}", strategy);
    let mut inv_exprs: Vec<ChcExpr> = vec![ChcExpr::Bool(false); preds.len()];

    // Divergence guard: track the positive-closure size across rounds.
    let mut prev_clo_size = 0usize;
    let mut stall = 0usize;
    let max_iters = max_iters();
    let stall_limit = stall_limit();

    for _iter in 0..max_iters {
        if Instant::now() >= deadline {
            return None;
        }
        // `inv_exprs` (the candidate, one formula per predicate) is used
        // read-only below for substitution and refreshed at the bottom of the
        // loop by [`learn_invariants`].

        // ── Search every clause for a counterexample ────────────────────────
        let mut refined = false;

        // Fact + rule clauses.
        for &clause in &rule_clauses {
            if Instant::now() >= deadline {
                return None;
            }
            let ClauseHead::Predicate(hpid, hargs) = &clause.head else {
                continue;
            };
            let hidx = hpid.index();
            // ¬I[head](hargs)
            let head_subst = canonical_subst(*hpid, hargs, problem);
            let head_inv = inv_exprs[hidx].substitute(&head_subst);

            let mut parts: Vec<ChcExpr> = Vec::new();
            if let Some(c) = &clause.body.constraint {
                parts.push(c.clone());
            }
            for (bpid, bargs) in &clause.body.predicates {
                let subst = canonical_subst(*bpid, bargs, problem);
                parts.push(inv_exprs[bpid.index()].substitute(&subst));
            }
            parts.push(ChcExpr::not(head_inv));
            let formula = ChcExpr::and_all(parts);

            // Ground-constant shortcut: a formula that simplifies to `false`
            // (e.g. a body invariant is `false`, or the head invariant is
            // `true`) is UNSAT — but the executor returns `Unknown` on a
            // variable-free constant, so evaluate it directly first.
            if matches!(
                evaluate_expr(&formula, &FxHashMap::default()),
                Some(SmtValue::Bool(false))
            ) {
                continue;
            }

            match backend.check_sat(&formula, query_timeout()) {
                SmtResult::Sat(model) => {
                    // Head point (may have free atoms ⇒ several completions).
                    let head_atoms_inst: Vec<ChcExpr> = atoms[hidx]
                        .iter()
                        .map(|a| a.substitute(&head_subst))
                        .collect();
                    let head_points = eval_points(&head_atoms_inst, &model, hidx)?;

                    if clause.body.predicates.is_empty() {
                        // Fact clause: the head point(s) MUST be positive (seed).
                        for hp in head_points {
                            push_unique(&mut pos, hp);
                            total_samples += 1;
                        }
                    } else {
                        // Rule clause: body points ⇒ head point (reachability
                        // edge). Record the implication so the positive closure
                        // can propagate through it.
                        let mut antecedents = Vec::new();
                        for (bpid, bargs) in &clause.body.predicates {
                            let bidx = bpid.index();
                            let batoms_inst: Vec<ChcExpr> = atoms[bidx]
                                .iter()
                                .map(|a| a.substitute(&canonical_subst(*bpid, bargs, problem)))
                                .collect();
                            let mut bp = eval_points(&batoms_inst, &model, bidx)?;
                            // A body atom is determined by the model; take the
                            // single completion (body atoms are constrained).
                            antecedents.push(bp.remove(0));
                        }
                        for hp in head_points {
                            impls.push(Impl {
                                antecedents: antecedents.clone(),
                                consequent: Some(hp),
                            });
                            total_samples += 1;
                        }
                    }
                    refined = true;
                    break;
                }
                r if r.is_unsat() => {}
                _ => {
                    ice_trace!("ABORT: rule clause check UNKNOWN (head pred {})", hidx);
                    return None; // Unknown ⇒ fail closed.
                }
            }
        }

        if !refined {
            // Query clauses: I[body] ∧ φ must be UNSAT.
            for &clause in &query_clauses {
                if Instant::now() >= deadline {
                    return None;
                }
                let mut parts: Vec<ChcExpr> = Vec::new();
                if let Some(c) = &clause.body.constraint {
                    parts.push(c.clone());
                }
                for (bpid, bargs) in &clause.body.predicates {
                    let subst = canonical_subst(*bpid, bargs, problem);
                    parts.push(inv_exprs[bpid.index()].substitute(&subst));
                }
                let formula = ChcExpr::and_all(parts);
                if matches!(
                    evaluate_expr(&formula, &FxHashMap::default()),
                    Some(SmtValue::Bool(false))
                ) {
                    continue;
                }
                match backend.check_sat(&formula, query_timeout()) {
                    SmtResult::Sat(model) => {
                        if clause.body.predicates.is_empty() {
                            // Constraint-only query is satisfiable ⇒ the abstract
                            // system is genuinely unsafe; no invariant exists.
                            return None;
                        }
                        let mut antecedents = Vec::new();
                        for (bpid, bargs) in &clause.body.predicates {
                            let bidx = bpid.index();
                            let batoms_inst: Vec<ChcExpr> = atoms[bidx]
                                .iter()
                                .map(|a| a.substitute(&canonical_subst(*bpid, bargs, problem)))
                                .collect();
                            let mut bp = eval_points(&batoms_inst, &model, bidx)?;
                            antecedents.push(bp.remove(0));
                        }
                        impls.push(Impl {
                            antecedents,
                            consequent: None,
                        });
                        total_samples += 1;
                        refined = true;
                        break;
                    }
                    r if r.is_unsat() => {}
                    _ => {
                        ice_trace!("ABORT: query clause check UNKNOWN");
                        return None;
                    }
                }
            }
        }

        if !refined {
            ice_trace!(
                "SOLVED after {} iters (pos={} impls={})",
                _iter,
                pos.len(),
                impls.len()
            );
            // No clause produced a counterexample ⇒ the candidate is inductive
            // and query-excluding on the abstract clauses. Build the model.
            let mut model = InvariantModel::new();
            for (i, pred) in preds.iter().enumerate() {
                let vars: Vec<ChcVar> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .map(|(c, s)| canonical_var(pred.id, c, s))
                    .collect();
                model.set(
                    pred.id,
                    PredicateInterpretation::new(vars, inv_exprs[i].clone()),
                );
            }
            return Some(model);
        }

        if total_samples > MAX_SAMPLES {
            ice_trace!("ABORT: sample cap {} exceeded", MAX_SAMPLES);
            return None;
        }

        // Divergence guard: if the reachable closure stops growing yet cexes
        // keep appearing, the atom lattice cannot pin the invariant (unbounded
        // column) — fail closed rather than churn to the deadline. Sized per
        // strategy: the concrete point closure (info-gain) or the partial-cube
        // region (mincube).
        let clo_size = match strategy {
            GenStrategy::InfoGain => forward_closure(&pos, &impls).len(),
            GenStrategy::MinCube => mincube_region(&pos, &impls).len(),
        };
        if clo_size > prev_clo_size {
            prev_clo_size = clo_size;
            stall = 0;
        } else {
            stall += 1;
            if stall > stall_limit {
                ice_trace!(
                    "ABORT: closure stalled at {} for {} rounds (iter {})",
                    clo_size,
                    stall,
                    _iter
                );
                return None;
            }
        }

        // ── Re-learn the trees consistent with the Horn samples ─────────────
        if _iter % 20 == 0 {
            ice_trace!(
                "iter {}: pos={} impls={} total_samples={} region/closure={}",
                _iter,
                pos.len(),
                impls.len(),
                total_samples,
                clo_size
            );
        }
        inv_exprs = match learn_invariants(strategy, preds.len(), &atoms, &pos, &impls, deadline) {
            Some(t) => t,
            None => {
                ice_trace!("ABORT: learn_invariants inconsistent at iter {}", _iter);
                return None;
            }
        };
    }

    None // iteration cap hit ⇒ fail closed.
}

/// Generic atom generator for the raw Real/Bool LRA transition-system lane
/// (task #27 LRA-Lin spike). Unlike [`build_atoms`], which reads cata
/// `ColumnTag`s, this derives atoms DIRECTLY from a predicate's argument sorts
/// — the generic frontend representation of a transition system's state vars:
///   * every Bool column `b` → the atom `b` (a 0/1 feature);
///   * every Real/Int column `v` → the interval atoms `v ≥ c` and `v ≤ c`
///     for each constant `c ∈ consts`;
///   * every ordered pair of same-sort numeric columns `(vi, vj)` → `vi ≤ vj`
///     and `vi = vj` (relational features).
///
/// Atoms are built over the predicate's CANONICAL argument vars (via
/// [`canonical_var`]), so [`canonical_subst`] instantiates them per application
/// exactly as the tag lane does. Count is bounded (`|bool| + 2·|const|·|num| +
/// |num|²`); the call site enforces [`max_atoms_per_pred`] / the u64 bitmask.
///
/// PROVEN-BUT-UNWIRED (task #27): the raw-LRA DT lane is exercised only by the
/// spike harness [`super::ice_dt_lra_spike`]; it is deliberately NOT wired into
/// any solve path, because on the diagnosed cav12 corpus the DT core's
/// refinement query returns SMT `Unknown` (the `ay-dpll`/`ay-lra` transition-
/// relation refutation blocker). Wiring it now would be a no-op on LRA-Lin.
#[allow(dead_code)]
pub(crate) fn generate_lra_atoms_for_pred(
    pid: PredicateId,
    arg_sorts: &[ChcSort],
    consts: &[i64],
) -> Vec<ChcExpr> {
    let var = |i: usize| ChcExpr::var(canonical_var(pid, i, &arg_sorts[i]));
    let mut pool: Vec<ChcExpr> = Vec::new();
    let push = |e: ChcExpr, pool: &mut Vec<ChcExpr>| {
        if !pool.iter().any(|p| *p == e) {
            pool.push(e);
        }
    };
    let is_real = |i: usize| matches!(arg_sorts[i], ChcSort::Real);
    let is_int = |i: usize| matches!(arg_sorts[i], ChcSort::Int);
    let bool_cols: Vec<usize> = (0..arg_sorts.len())
        .filter(|&i| matches!(arg_sorts[i], ChcSort::Bool))
        .collect();
    let num_cols: Vec<usize> = (0..arg_sorts.len())
        .filter(|&i| is_real(i) || is_int(i))
        .collect();

    // (1) Boolean columns as 0/1 atoms.
    for &i in &bool_cols {
        push(var(i), &mut pool);
    }
    // (2) Interval atoms per numeric column at each constant.
    for &i in &num_cols {
        let lit = |c: i64| {
            if is_real(i) {
                ChcExpr::Real(c, 1)
            } else {
                ChcExpr::int(i128::from(c))
            }
        };
        for &c in consts {
            push(ChcExpr::ge(var(i), lit(c)), &mut pool);
            push(ChcExpr::le(var(i), lit(c)), &mut pool);
        }
    }
    // (3) Pairwise relational atoms among same-sort numeric columns.
    for a in 0..num_cols.len() {
        for b in (a + 1)..num_cols.len() {
            let (i, j) = (num_cols[a], num_cols[b]);
            if is_real(i) != is_real(j) {
                continue; // never mix Real and Int in one comparison
            }
            push(ChcExpr::le(var(i), var(j)), &mut pool);
            push(ChcExpr::eq(var(i), var(j)), &mut pool);
        }
    }
    pool
}

/// Run the Horn-ICE DT learner over a RAW Real/Bool CHC transition system,
/// generating the atom set with [`generate_lra_atoms_for_pred`] over the
/// integer constant set `consts`. LRA-Lin spike entry (task #27).
///
/// Candidate generator ONLY — the returned model is inductive + query-excluding
/// on the sampled points and re-checked against every clause by the internal
/// SMT loop, but NOT trusted: the caller re-certifies it on the ORIGINAL
/// clauses. Fails closed to `None` (atom-cap overflow, loop bound, or any
/// indeterminate SMT query).
///
/// PROVEN-BUT-UNWIRED (task #27): see [`generate_lra_atoms_for_pred`] — the
/// spike harness is the only caller; the raw-LRA lane is blocked downstream by
/// the `ay-dpll`/`ay-lra` transition-relation refutation `Unknown`, not by this
/// learner.
#[allow(dead_code)]
pub(crate) fn solve_lra_ice_dt(
    problem: &ChcProblem,
    consts: &[i64],
    deadline: Instant,
) -> Option<InvariantModel> {
    let preds = problem.predicates();
    if preds.is_empty() {
        return None;
    }
    let mut atoms: Vec<Vec<ChcExpr>> = Vec::with_capacity(preds.len());
    for pred in preds {
        let a = generate_lra_atoms_for_pred(pred.id, &pred.arg_sorts, consts);
        ice_trace!(
            "LRA pred {} ({}) -> {} atoms",
            pred.id.index(),
            pred.name,
            a.len()
        );
        if a.len() > max_atoms_per_pred() {
            ice_trace!(
                "ABORT: LRA pred {} has {} atoms > cap {}",
                pred.name,
                a.len(),
                max_atoms_per_pred()
            );
            return None;
        }
        atoms.push(a);
    }
    run_ice_dt_core(problem, atoms, deadline)
}

/// Build the per-predicate candidate invariant formulas for one Horn-ICE round
/// under the active [`GenStrategy`]. Both strategies share the SAME sampled
/// points and the SAME soundness contract (candidate generator only, caller
/// re-certifies); they differ ONLY in how the positive region is generalized.
/// Returns `None` (fail closed) when the samples are inconsistent under the
/// atom set (a query goal proven reachable from the facts, or an info-gain
/// deadline miss).
fn learn_invariants(
    strategy: GenStrategy,
    n_preds: usize,
    atoms: &[Vec<ChcExpr>],
    pos: &[Cube],
    impls: &[Impl],
    deadline: Instant,
) -> Option<Vec<ChcExpr>> {
    match strategy {
        GenStrategy::InfoGain => {
            let trees = learn_trees(n_preds, atoms, pos, impls, deadline)?;
            Some((0..n_preds).map(|i| trees[i].to_expr(&atoms[i])).collect())
        }
        GenStrategy::MinCube => mincube_invariants(n_preds, atoms, pos, impls),
    }
}

/// Union-of-cubes (minimal-positive) generalization. The candidate for each
/// predicate is the DISJUNCTION, over the positive-region cubes of that
/// predicate, of each cube's PARTIAL minterm — the conjunction of every atom the
/// cube DETERMINES (its `care` bits), at that atom's polarity, and NOTHING for
/// the atoms the sampling left free. This is the characteristic function of the
/// sampled reachable atom-patterns, GENERALIZED exactly along the columns the
/// counterexample models never pinned: it admits those patterns (plus arbitrary
/// values on the don't-care columns) and nothing else. Two consequences:
///  * the inductiveness check can only ever refute from a body already in the
///    region (its determined atoms must match a cube) ⇒ each rule cex GROWS the
///    region by its new post-state, bounded by the reachable-pattern count —
///    never the info-gain "+1 non-reachable edge per round" divergence;
///  * an unconstrained init (dozens of free real-column atoms) collapses to ONE
///    small cube over the columns it DOES pin (e.g. the three Booleans) instead
///    of an unbounded enumeration of zero-extended completions.
///
/// Fails closed to `None` when a query goal is covered by the region (the error
/// is reachable from the facts under this atom set ⇒ the atoms cannot prove
/// safety here) — identical in spirit to [`learn_trees`]'s coarse-atom guard.
fn mincube_invariants(
    n_preds: usize,
    atoms: &[Vec<ChcExpr>],
    pos: &[Cube],
    impls: &[Impl],
) -> Option<Vec<ChcExpr>> {
    let region = mincube_region(pos, impls);

    // Query goal covered by the region ⇒ error reachable from the facts.
    for imp in impls {
        if imp.consequent.is_none()
            && imp
                .antecedents
                .iter()
                .all(|a| region.iter().any(|c| c.subsumes(a)))
        {
            ice_trace!("mincube: query goal reachable in region ⇒ unsafe/coarse");
            return None;
        }
    }

    let mut out: Vec<ChcExpr> = Vec::with_capacity(n_preds);
    for i in 0..n_preds {
        let mut cubes: Vec<ChcExpr> = Vec::new();
        for c in &region {
            if c.pred == i {
                cubes.push(cube_of_ppoint(&atoms[i], c.value, c.care));
            }
        }
        out.push(match cubes.len() {
            0 => ChcExpr::Bool(false),
            1 => cubes.pop().unwrap(),
            _ => ChcExpr::or_all(cubes),
        });
    }
    Some(out)
}

/// The positive REGION under the mincube strategy: the least antichain of cubes
/// containing the fact-seed cubes `pos` and closed under the reachability
/// implications — a consequent is admitted once EVERY antecedent is subsumed by
/// the current region (`covered`). Query implications (`consequent == None`) do
/// not propagate. Kept minimal (an antichain) via [`insert_cube`] so the
/// candidate DNF stays compact.
fn mincube_region(pos: &[Cube], impls: &[Impl]) -> Vec<Cube> {
    let mut region: Vec<Cube> = Vec::new();
    for &p in pos {
        insert_cube(&mut region, p);
    }
    loop {
        let mut changed = false;
        for imp in impls {
            if let Some(cons) = imp.consequent {
                if !region.iter().any(|c| c.subsumes(&cons))
                    && imp
                        .antecedents
                        .iter()
                        .all(|a| region.iter().any(|c| c.subsumes(a)))
                {
                    insert_cube(&mut region, cons);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    region
}

/// Insert `new` into a cube antichain: drop it if an existing cube already
/// covers it, else remove every existing cube `new` covers and push it. Keeps
/// the region free of redundant (subsumed) cubes.
fn insert_cube(region: &mut Vec<Cube>, new: Cube) {
    if region.iter().any(|c| c.subsumes(&new)) {
        return;
    }
    region.retain(|c| !new.subsumes(c));
    region.push(new);
}

/// The PARTIAL minterm of a cube over `atoms`: the conjunction of `atoms[j]`
/// (when the cube's `value` bit `j` is set) or `¬atoms[j]` (when clear) for
/// every atom `j` the cube DETERMINES (its `care` bit `j` set); don't-care
/// atoms contribute no literal. An all-don't-care cube is `true`.
fn cube_of_ppoint(atoms: &[ChcExpr], value: u64, care: u64) -> ChcExpr {
    let mut lits: Vec<ChcExpr> = Vec::with_capacity(atoms.len());
    for (j, a) in atoms.iter().enumerate() {
        let bit = 1u64 << j;
        if care & bit == 0 {
            continue; // don't-care atom — no literal
        }
        if value & bit != 0 {
            lits.push(a.clone());
        } else {
            lits.push(ChcExpr::not(a.clone()));
        }
    }
    match lits.len() {
        0 => ChcExpr::Bool(true),
        1 => lits.pop().unwrap(),
        _ => ChcExpr::and_all(lits),
    }
}

/// Learn one decision tree per predicate consistent with the Horn samples
/// (one Horn-ICE-DT round). The labeling is derived FRESH each round — never
/// accumulated — as the least Horn model over the SAMPLED points:
///  * positive = the forward closure of the fact seeds under the reachability
///    edges (points genuinely reachable from a fact in ≤k sampled steps);
///  * negative = every other sampled point (the tightest consistent labeling:
///    a point not yet shown reachable is excluded, and if a later cex shows it
///    reachable the closure grows and it flips to positive next round — no
///    permanent commitment, so no spurious conflict).
///
/// A query goal all of whose antecedents lie in the closure means the error is
/// reachable from the facts ⇒ the atoms cannot prove safety here ⇒ `None`
/// (fail closed). Every candidate is re-checked against the clauses by the
/// caller's SMT loop, which drives the next sample.
fn learn_trees(
    n_preds: usize,
    atoms: &[Vec<ChcExpr>],
    pos: &[Cube],
    impls: &[Impl],
    deadline: Instant,
) -> Option<Vec<Dt>> {
    let clo = forward_closure(pos, impls);

    // Query goal fully inside the closure ⇒ error reachable from the facts.
    for imp in impls {
        if imp.consequent.is_none() && imp.antecedents.iter().all(|a| clo.contains(&a.concrete())) {
            ice_trace!("learn_trees: query goal reachable in closure ⇒ unsafe/coarse");
            return None;
        }
    }

    // Collect every sampled point (concrete projection); label by closure
    // membership.
    let mut sampled: std::collections::HashSet<Point> = clo.iter().copied().collect();
    for p in pos {
        sampled.insert(p.concrete());
    }
    for imp in impls {
        for a in &imp.antecedents {
            sampled.insert(a.concrete());
        }
        if let Some(c) = imp.consequent {
            sampled.insert(c.concrete());
        }
    }

    let mut trees: Vec<Dt> = Vec::with_capacity(n_preds);
    for i in 0..n_preds {
        let mut data: Vec<(u64, bool)> = Vec::new();
        for &(pi, bits) in &sampled {
            if pi == i {
                data.push((bits, clo.contains(&(pi, bits))));
            }
        }
        trees.push(build_tree(&data, atoms[i].len(), deadline)?);
    }
    Some(trees)
}

/// Forward positive closure over CONCRETE points (info-gain lane): the least
/// set containing the `pos` seeds' concrete projections and closed under the
/// reachability implications (`antecedents ⊆ C ⇒ consequent ∈ C`). Query
/// implications (`consequent == None`) do not propagate. Cubes are projected
/// via [`Cube::concrete`], so this is bit-for-bit the pre-partial-cube closure.
fn forward_closure(pos: &[Cube], impls: &[Impl]) -> std::collections::HashSet<Point> {
    let mut c: std::collections::HashSet<Point> = pos.iter().map(Cube::concrete).collect();
    loop {
        let mut changed = false;
        for imp in impls {
            if let Some(cons) = imp.consequent {
                let cc = cons.concrete();
                if !c.contains(&cc) && imp.antecedents.iter().all(|a| c.contains(&a.concrete())) {
                    c.insert(cc);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    c
}

/// Evaluate one instantiated atom under `model`, resolving every variable the
/// model leaves UNASSIGNED to its sort's zero (Real `0` / Int `0` / Bool
/// `false`). The result is the atom's truth in the single concrete state
/// `model ∪ {unassigned ↦ 0}`. Returns `None` only if the atom is STILL
/// indeterminate after the zero-extension (e.g. an opaque/array term), so the
/// caller fails closed.
///
/// # Why zero-extension (joint) rather than per-atom free branching
///
/// A counterexample model need not pin every state column: a fact whose reals
/// are entirely unconstrained (e.g. an LRA transition system's `init`), or a
/// rule with havoc columns, leaves those variables free. Evaluating each such
/// atom independently over BOTH polarities enumerates `2^k` completions — which
/// (a) blows past any cap on an unconstrained init (k ≈ #real-atoms) and (b)
/// over-approximates: it fabricates bit-combos that are NOT jointly satisfiable
/// (e.g. `v≤0 ∧ v≥1`), which then read as spurious pos/neg conflicts. Anchoring
/// on ONE jointly-consistent completion (the zero extension is always a genuine
/// model of the clause body) avoids both. Any OTHER completion the invariant
/// must also cover is recovered by the outer SMT loop: it re-checks the clause,
/// and an uncovered completion resurfaces as the next counterexample (the SMT
/// solver pins the relevant column that round). Soundness is unchanged — the
/// caller re-certifies every candidate on the ORIGINAL clauses.
fn eval_atom_zero_extended(atom: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> Option<bool> {
    let subst: Vec<(ChcVar, ChcExpr)> = atom
        .vars()
        .into_iter()
        .filter(|v| !model.contains_key(&v.name))
        .map(|v| {
            let zero = match v.sort {
                ChcSort::Real => ChcExpr::Real(0, 1),
                ChcSort::Bool => ChcExpr::Bool(false),
                _ => ChcExpr::int(0),
            };
            (v, zero)
        })
        .collect();
    let resolved = if subst.is_empty() {
        atom.clone()
    } else {
        atom.substitute(&subst)
    };
    match evaluate_expr(&resolved, model) {
        Some(SmtValue::Bool(b)) => Some(b),
        _ => None,
    }
}

/// Free-atom completion policy: enumerate every polarity when at most this many
/// atoms are indeterminate (the compact cata lane relies on covering ALL abstract
/// completions of an unconstrained abstract column, and only ever has a handful);
/// beyond it, collapse to a single jointly-consistent completion via
/// [`eval_atom_zero_extended`] — which is what makes an LRA transition system's
/// wholly-unconstrained `init` (dozens of free real-column atoms) tractable
/// instead of a `2^k` blow-up.
const FREE_ENUM_THRESHOLD: usize = 6;

/// Evaluate the instantiated atoms of one predicate application under a model,
/// returning the resulting point(s). Atoms the model leaves indeterminate are
/// FREE. Up to [`FREE_ENUM_THRESHOLD`] free atoms are enumerated over both
/// polarities (every completion — the cata-lane discipline). Beyond that, the
/// free atoms are resolved JOINTLY by zero-extending the model to a single
/// consistent completion ([`eval_atom_zero_extended`]); the outer SMT loop
/// recovers any other completion the invariant must cover as a later
/// counterexample. Returns `None` if a free atom stays indeterminate even after
/// zero-extension (fail closed).
fn eval_points(
    atoms_inst: &[ChcExpr],
    model: &FxHashMap<String, SmtValue>,
    pred_index: usize,
) -> Option<Vec<Cube>> {
    let m = atoms_inst.len();
    debug_assert!(m <= 64);
    // `full_care` marks every atom index as DETERMINED (all bits in [0, m)).
    let full_care = if m >= 64 { u64::MAX } else { (1u64 << m) - 1 };
    let mut base = 0u64;
    let mut free: Vec<usize> = Vec::new();
    for (i, atom) in atoms_inst.iter().enumerate() {
        match evaluate_expr(atom, model) {
            Some(SmtValue::Bool(true)) => base |= 1u64 << i,
            Some(SmtValue::Bool(false)) => {}
            _ => free.push(i),
        }
    }
    if free.is_empty() {
        return Some(vec![Cube {
            pred: pred_index,
            value: base,
            care: full_care,
        }]);
    }
    if free.len() > FREE_ENUM_THRESHOLD {
        // Too many free atoms to enumerate (unconstrained init / heavy havoc):
        // resolve them JOINTLY to their zero-extension for the concrete `value`
        // (so the info-gain projection is unchanged) but mark them DON'T-CARE in
        // `care`. Under mincube this is the partial-cube generalization that
        // collapses an unconstrained init to a single small cube; under
        // info-gain the concrete projection ignores `care`, so behavior is
        // identical to the old zero-extension.
        ice_trace!(
            "pred {} cex has {} FREE atoms {:?} — zero-extending value, DON'T-CARE in cube",
            pred_index,
            free.len(),
            free
        );
        let mut bits = base;
        let mut care = full_care;
        for &fi in &free {
            care &= !(1u64 << fi); // free atom ⇒ don't-care
            match eval_atom_zero_extended(&atoms_inst[fi], model) {
                Some(true) => bits |= 1u64 << fi,
                Some(false) => {}
                None => {
                    ice_trace!(
                        "pred {} atom {} indeterminate after zero-extension",
                        pred_index,
                        fi
                    );
                    return None; // still indeterminate ⇒ fail closed.
                }
            }
        }
        return Some(vec![Cube {
            pred: pred_index,
            value: bits,
            care,
        }]);
    }
    ice_trace!(
        "pred {} cex has {} FREE atoms {:?}",
        pred_index,
        free.len(),
        free
    );
    let n = 1usize << free.len();
    let mut out = Vec::with_capacity(n);
    for combo in 0..n {
        let mut bits = base;
        for (k, &fi) in free.iter().enumerate() {
            if combo & (1 << k) != 0 {
                bits |= 1u64 << fi;
            }
        }
        out.push(Cube {
            pred: pred_index,
            value: bits,
            care: full_care,
        });
    }
    Some(out)
}

/// Push a fact-seed cube into `pos`, deduplicating by exact equality (predicate
/// + value + care). Exact dedup — NOT subsumption — so the info-gain lane's
/// concrete seed set is unchanged; the mincube lane re-minimizes `pos` into an
/// antichain inside [`mincube_region`] anyway.
fn push_unique(v: &mut Vec<Cube>, p: Cube) {
    if !v.contains(&p) {
        v.push(p);
    }
}

/// Learn an information-gain decision tree over the boolean atom features.
/// `n_atoms` bounds the feature indices. Returns `None` only on deadline.
fn build_tree(data: &[(u64, bool)], n_atoms: usize, deadline: Instant) -> Option<Dt> {
    // Deduplicate; a duplicate bitmask with opposing labels is a genuine
    // conflict the atom set cannot separate — but rather than fail the whole
    // learner (the outer SMT loop already guards soundness), we let such a node
    // fall to a majority leaf, and the SMT check will drive further refinement
    // or the loop bound will fail closed. This keeps the learner total.
    build_tree_rec(data, n_atoms, 0, deadline)
}

fn build_tree_rec(
    data: &[(u64, bool)],
    n_atoms: usize,
    depth: usize,
    deadline: Instant,
) -> Option<Dt> {
    if Instant::now() >= deadline {
        return None;
    }
    if data.is_empty() {
        // No evidence ⇒ default FALSE (least element: excludes by default).
        return Some(Dt::Leaf(false));
    }
    let pos = data.iter().filter(|(_, l)| *l).count();
    let neg = data.len() - pos;
    if pos == 0 {
        return Some(Dt::Leaf(false));
    }
    if neg == 0 {
        return Some(Dt::Leaf(true));
    }
    if depth >= MAX_TREE_DEPTH {
        return Some(Dt::Leaf(pos >= neg));
    }

    // Pick the atom with the highest information gain that actually partitions
    // the data into two non-empty subsets.
    let base_entropy = entropy(pos, data.len());
    let mut best: Option<(usize, f64)> = None;
    for atom in 0..n_atoms {
        let mask = 1u64 << atom;
        let (mut hp, mut hn, mut lp, mut ln) = (0usize, 0usize, 0usize, 0usize);
        for (bits, lab) in data {
            let hi = bits & mask != 0;
            match (hi, *lab) {
                (true, true) => hp += 1,
                (true, false) => hn += 1,
                (false, true) => lp += 1,
                (false, false) => ln += 1,
            }
        }
        let hi_n = hp + hn;
        let lo_n = lp + ln;
        if hi_n == 0 || lo_n == 0 {
            continue; // does not partition
        }
        let total = data.len() as f64;
        let gain = base_entropy
            - (hi_n as f64 / total) * entropy(hp, hi_n)
            - (lo_n as f64 / total) * entropy(lp, lo_n);
        match best {
            Some((_, g)) if g >= gain => {}
            _ => best = Some((atom, gain)),
        }
    }

    let Some((atom, _)) = best else {
        // No atom partitions the (impure) data ⇒ identical feature vectors with
        // opposing labels. Majority leaf; the SMT loop refines or bounds out.
        return Some(Dt::Leaf(pos >= neg));
    };

    let mask = 1u64 << atom;
    let hi_data: Vec<(u64, bool)> = data
        .iter()
        .copied()
        .filter(|(b, _)| b & mask != 0)
        .collect();
    let lo_data: Vec<(u64, bool)> = data
        .iter()
        .copied()
        .filter(|(b, _)| b & mask == 0)
        .collect();
    let hi = build_tree_rec(&hi_data, n_atoms, depth + 1, deadline)?;
    let lo = build_tree_rec(&lo_data, n_atoms, depth + 1, deadline)?;
    Some(Dt::Node {
        atom,
        lo: Box::new(lo),
        hi: Box::new(hi),
    })
}

/// Binary entropy of `p` positives out of `n` (in bits). `0` for a pure set.
fn entropy(p: usize, n: usize) -> f64 {
    if p == 0 || p == n {
        return 0.0;
    }
    let pp = p as f64 / n as f64;
    let pn = 1.0 - pp;
    -(pp * pp.log2() + pn * pn.log2())
}

#[cfg(test)]
mod mincube_tests {
    use super::*;

    fn cube(pred: usize, value: u64, care: u64) -> Cube {
        Cube { pred, value, care }
    }

    /// A more-general cube (fewer `care` bits) subsumes a more-specific one that
    /// agrees on the cared atoms; polarity mismatch and predicate mismatch both
    /// break subsumption; a fully-free cube (`care == 0`) covers everything of
    /// its predicate.
    #[test]
    fn cube_subsumption_semantics() {
        // atom0=1, atom1 don't-care  subsumes  atom0=1, atom1=0 and =1.
        let general = cube(0, 0b01, 0b01);
        assert!(general.subsumes(&cube(0, 0b01, 0b11)));
        assert!(general.subsumes(&cube(0, 0b11, 0b11)));
        // ... but not a state with atom0=0.
        assert!(!general.subsumes(&cube(0, 0b10, 0b11)));
        // A more-specific cube never subsumes a more-general one.
        assert!(!cube(0, 0b01, 0b11).subsumes(&general));
        // Different predicate ⇒ never subsumes.
        assert!(!cube(1, 0b01, 0b01).subsumes(&cube(0, 0b01, 0b01)));
        // All-don't-care cube covers any state of its predicate.
        assert!(cube(0, 0, 0).subsumes(&cube(0, 0b1111, 0b1111)));
    }

    /// The partial minterm emits a literal only for the cared atoms, at the
    /// polarity `value` dictates; don't-care atoms contribute nothing.
    #[test]
    fn partial_cube_drops_dont_cares() {
        let atoms = vec![
            ChcExpr::var(ChcVar::new("a", ChcSort::Bool)),
            ChcExpr::var(ChcVar::new("b", ChcSort::Bool)),
            ChcExpr::var(ChcVar::new("c", ChcSort::Bool)),
        ];
        // care only atom0(true) and atom2(false); atom1 free.
        let e = cube_of_ppoint(&atoms, 0b001, 0b101);
        let s = InvariantModel::expr_to_smtlib(&e);
        assert!(s.contains('a'), "cared true atom present: {s}");
        assert!(s.contains('c'), "cared false atom present: {s}");
        assert!(!s.contains('b'), "don't-care atom must be dropped: {s}");
        // All-don't-care ⇒ `true`.
        assert!(matches!(cube_of_ppoint(&atoms, 0, 0), ChcExpr::Bool(true)));
    }

    /// The mincube region collapses an unconstrained "init" (all data atoms
    /// don't-care, only a control atom pinned) into a SINGLE cube instead of
    /// enumerating every zero-extended completion — the s3_srvr_4 init-explosion
    /// fix — and propagates one reachability edge from a covered antecedent.
    #[test]
    fn region_generalizes_free_init_and_propagates() {
        // Seed: control atom0=1, data atoms 1..4 all don't-care (an init whose
        // reals were unconstrained).
        let seed = cube(0, 0b0001, 0b0001);
        // Edge: from a body with atom0=1, arbitrary data (covered by the seed
        // regardless of its data atoms) to a genuinely NEW head that flips the
        // control atom0 to 0 and pins atom1 (a distinct reachable pattern the
        // seed does not cover).
        let edge = Impl {
            antecedents: vec![cube(0, 0b0001, 0b1111)],
            consequent: Some(cube(0, 0b0010, 0b1111)),
        };
        let region = mincube_region(&[seed], &[edge]);
        // Region holds exactly two cubes: the general init seed + the reached head.
        assert_eq!(region.len(), 2, "region: {region:?}");
        assert!(region.iter().any(|c| *c == seed));
        assert!(region.iter().any(|c| c.value == 0b0010 && c.care == 0b1111));
        // The seed covers every data completion of atom0=1 ⇒ no enumeration of
        // the init's free columns (the divergence fix).
        assert!(seed.subsumes(&cube(0, 0b1101, 0b1111)));
        assert!(seed.subsumes(&cube(0, 0b0111, 0b1111)));
        // A head that stays atom0=1 (already covered by the seed) is NOT re-added.
        let edge2 = Impl {
            antecedents: vec![cube(0, 0b0001, 0b1111)],
            consequent: Some(cube(0, 0b0101, 0b1111)),
        };
        assert_eq!(mincube_region(&[seed], &[edge2]).len(), 1);
    }

    /// A consequent whose antecedent is NOT covered by the region never enters
    /// it (reachability discipline preserved under partial cubes).
    #[test]
    fn region_blocks_uncovered_antecedent() {
        let seed = cube(0, 0b0001, 0b0001); // atom0=1
        let edge = Impl {
            antecedents: vec![cube(0, 0b0000, 0b0001)], // needs atom0=0 — not covered
            consequent: Some(cube(0, 0b1000, 0b1111)),
        };
        let region = mincube_region(&[seed], &[edge]);
        assert_eq!(
            region.len(),
            1,
            "uncovered edge must not propagate: {region:?}"
        );
    }
}
