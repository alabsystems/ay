// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ground refutation over the RAW authored roots, found by proof-producing
//! congruence closure with read-over-write and closed bit-vector evaluation.
//!
//! Elaboration folds closed index spellings and missed writes away
//! (`(select (store D #x40 v) #x41)` interns as `(select D #x41)`,
//! `(bvadd #x3f #x01)` as `#x40`), and preprocessing substitutes aliases. The
//! refutation of the folded problem then reaches the datatype/array solvers
//! with no recorded argument and ships as a whole-problem `hole`, which the
//! mandatory strict certification correctly withholds, although the authored
//! problem is refuted by ground equality reasoning a checker can replay:
//!
//! ```text
//! (assert (= a b))
//! (assert (= (select (store (fld_data (fld_lits (select a #x09))) #x40 #x07) #x41) #x08))
//! (assert (= (select (fld_data (fld_lits (select b #x09))) #x41) #x09))
//! ```
//!
//! This lane decides that fragment directly over the raw re-interns of the
//! parsed assertions, so every term prints exactly as authored and no surface
//! bridge is needed. Native API rows instead contribute their exact paired
//! concrete source roots, already in the frozen problem scope; the reserved
//! parsed-row marker is never interpreted as an assumption or a symbol.
//!
//! RECORD CONSTANTS are the one place a raw re-intern cannot be print
//! faithful. A declared constant of a single-constructor datatype elaborates
//! to its constructor over solver-invented field constants `k_i` with private
//! identities (`a` interns as `(mkVec k_ptr k_len ..)`, `(len a)` as `k_len`),
//! and each field prints back
//! as `(len a)` only through the frontend's validated field renderings
//! (`dt_field_surface_overrides`). A selector read over such a constant fails
//! raw interning, which dropped the whole assertion, and a record equality
//! `(= a v0)` raw-interns as an equality of two constructor applications,
//! which only injectivity (a datatype rule pinned carcara lacks) could open.
//! For exactly two shapes the search therefore also reads the ELABORATED twin
//! of the parsed assertion from the exact concrete authored scope (a premise
//! every other lane may already assume):
//!
//! * an assertion whose raw re-intern is unavailable and whose twin reads a
//!   record field: the twin spells its field reads as field constants,
//!   which print as the authored reads;
//! * an equality between two record constants: the twin is the field-wise
//!   conjunction, which the exporter presents as `cong` over the authored
//!   `(= a v0)` plus `and_neg`.
//!
//! An equality between a record constant and a constructor APPLICATION
//! (`(= v0 (mkVec ..))`) gets no twin: its field-wise reading is
//! selector-over-constructor, which pinned carcara cannot check, so offering
//! it would only let an explanation route through an unprintable premise.
//!
//! It is a textbook congruence closure (Nelson-Oppen / Downey-Sethi-Tarjan
//! signature merging, with Nieuwenhuis-Oliveras style explanations
//! recovered from the justification graph) extended by
//! edge producers, each named after the strict-checked lemma that proves it:
//!
//! * `Authored` — an exact authored equality root (`assume`);
//! * `Congruent` — same symbol, pairwise merged arguments (`EufCongruent`);
//! * `Evaluated` — a closed bit-vector term and the constant it equals
//!   (`BvBitBlast`, decided by the checker's own recognizer);
//! * `ReadHit` / `ReadMiss` — McCarthy's read-over-write axioms
//!   (`ArraySelectStore`), the miss only when the two index classes hold two
//!   different bit-vector constants;
//! * `ReadChain` — a direct source store-hit equality (`ArrayRowChain`),
//!   with each skipped source key discharged by a strict array-free BV
//!   disequality and any source alias explained from earlier edges.
//!
//! Boolean facts ride on top (`facts.rs`): authored atoms and conjuncts
//! (`and_pos`), closed bit-vector literals (`BvBitBlast`), predicate
//! congruence (`EufCongruentPred`), and unit propagation over authored clauses
//! (`or`/`implies`) and ground instances of single-binder authored universals
//! (`instances.rs`, `forall_inst`). Every propagated fact is forced; no case
//! split is ever made. Candidates using authored clauses must retain exact
//! concrete source authority for every reachable assumption.
//!
//! It closes on two different bit-vector constants in one class, an authored
//! disequality whose sides merged, a complementary pair of facts, or an
//! instance clause every literal of which is refuted. The emitted candidate
//! chains each explanation with `EufTransitive`.
//!
//! NOTHING IS TAKEN ON THE PRODUCER'S WORD: every lemma kind above has a strict
//! validator that re-derives its clause, the candidate must derive the empty
//! clause with no trust step before any raw root is admitted as a premise,
//! and it is committed only through [`Executor::commit_if_strictly_checked`].
//! It is also kept only when the document the exporter will PUBLISH has no
//! `hole` or `trust` step and renders at all (`screen.rs`): the screen runs
//! the two post-cascade presentation passes, which re-spell reachable assumes
//! and `forall_inst` instances from the problem text, on a clone of the
//! committed proof and judges the bytes they leave. A universal whose
//! elaborated body is not its authored body (`bvsge` normalized to `bvsle`,
//! `(not (distinct ..))` to `=`), or a record query whose authored `and` the
//! elaborated twin flattened, is therefore declined instead of publishing a
//! `holey` or export-refused `unsat`. The screen cannot see a hole-free step
//! the external checker refuses; the lemma shapes the printer spells in a form
//! pinned Carcara refuses are kept out of the search ([`EVALUATED_OPERATORS`]).
//! A closure this lane gets wrong costs completeness (the verdict stays the
//! `unknown` it was), never soundness.

use super::*;

mod authored_clauses;
mod bv_intrinsics;
mod congruence;
mod early;
mod emit;
mod emit_facts;
mod facts;
mod goal;
mod goal_boolean;
mod goal_read_range;
mod instances;
mod native_roots;
mod offset;
mod packing;
mod packing_emit;
mod read_chain;
mod read_chain_emit;
mod read_range;
mod saturate;
mod screen;
mod slice;
mod state;
#[cfg(test)]
mod tests;
mod work;

use early::closure_note;
use facts::GroundSearch;
use instances::FlatForall;
use state::{EdgeReason, GroundClosure};
use work::SharedGroundWork;

/// Distinct native roots and ordinary parsed rows beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Duplicate native rows are bounded separately from their distinct roots.
const MAX_NATIVE_AUTHORED_ROWS: usize = 128;
/// Registered terms (authored subterms, introduced base reads and slice
/// rewrites). A translation-validation root names one 64-bit word per SSA
/// value on both sides of the claim. The exact original TY conditional
/// scalar-memory query has 1615 raw terms before saturation, so 1024 declined
/// before proposing any word-level proof. This remains a bounded producer
/// search capacity; strict replay, proof/byte meters and grades are unchanged.
pub(in crate::executor::proof) const MAX_NODES: usize = 2_048;
/// Recorded merges.
const MAX_EDGES: usize = 2_048;
/// Saturation rounds; each round is linear in the registered terms.
const MAX_ROUNDS: usize = 16;
/// Recognizer calls one search may spend proposing `Evaluated` edges and
/// `Closed` facts.
const MAX_RECOGNIZER_PROBES: usize = 64;
/// Nodes one closed-term test may visit.
const MAX_CLOSED_TERM_WORK: usize = 256;

/// Bit-vector operators whose closed applications are worth proposing to the
/// recognizer. A work filter: the recognizer decides every edge.
///
/// It also keeps out every operator whose closed evaluation the printer
/// spells in a form pinned Carcara (1.1.0, git 9a352ee) rejects, because the
/// wire screen sees `hole` and `trust` steps, not a checker's verdict:
/// `bvudiv`/`bvurem` print through `complete_blast`'s divider, which is
/// clean `5390f432b8`'s fixed long division (e9b297e37), and pinned Carcara
/// refuses every such `bitblast_udiv`/`bitblast_urem` step ("expected terms
/// to be equal"); a closed `zero_extend` can print as `refl` against its
/// `concat` spelling ("reflexivity failed"), which it refuses too. Measured
/// on 938ec0327 with the store-hit shape `(select (store (store A t 1) IDX
/// 2) t)`: all twenty `bvudiv`/`bvurem` indices (quotient, remainder, zero
/// divisor; 4 to 64 bits) and five of ten `zero_extend` indices (16 to 64
/// bits) went from `unknown` to a Carcara-`invalid` `unsat`. Leaving them out
/// costs completeness only: the verdict stays the `unknown` it was.
const EVALUATED_OPERATORS: &[&str] = &[
    "bvadd", "bvmul", "bvsub", "bvneg", "bvnot", "bvand", "bvor", "bvxor", "bvshl", "bvlshr",
    "concat", "extract",
];

/// The roots of one search, and which of them are raw re-interns (only those
/// enter the raw premise ledger; twins and native roots are already in the
/// concrete scope).
#[derive(Default)]
pub(super) struct GroundRoots {
    pub(super) raw: Vec<TermId>,
    pub(super) search: Vec<TermId>,
}

/// Whether `root` is an equality between two record constants: each side is
/// a constructor application all of whose arguments are solver-invented field
/// constants with a validated selector rendering (`fields`).
fn is_record_constant_equality(
    terms: &TermStore,
    root: TermId,
    fields: &ay_core::kani_compat::DetHashMap<TermId, String>,
) -> bool {
    let Some((lhs, rhs)) = decode_eq_local(terms, root) else {
        return false;
    };
    [lhs, rhs].into_iter().all(|side| {
        matches!(terms.get(side), TermData::App(_, args)
            if !args.is_empty() && args.iter().all(|arg| fields.contains_key(arg)))
    })
}

/// Whether `root` reads a record field (holds a field constant of `fields`)
/// and contains no binder, within [`MAX_NODES`] distinct nodes.
fn is_binder_free_record_read(
    terms: &TermStore,
    root: TermId,
    fields: &ay_core::kani_compat::DetHashMap<TermId, String>,
) -> bool {
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut pending = vec![root];
    let mut reads_field = false;
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_NODES {
            return false;
        }
        reads_field |= fields.contains_key(&term);
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return false,
            TermData::App(_, args) => pending.extend(args.iter().copied()),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then, other) => {
                pending.extend([*condition, *then, *other]);
            }
            _ => {}
        }
    }
    reads_field
}

/// What the saturated closure refutes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ClosureConflict {
    /// Two different bit-vector constants share a class.
    ConstantClash(TermId, TermId),
    /// The sides of an authored `(not (= lhs rhs))` share a class.
    Disequality {
        root: TermId,
        equality: TermId,
        lhs: TermId,
        rhs: TermId,
    },
    /// Facts `positive` (an atom) and `negative` (its negation) both hold.
    Complementary { positive: usize, negative: usize },
    /// Every literal of instance clause `clause` is refuted by these facts.
    RefutedClause { clause: usize, refuting: Vec<usize> },
    /// Fact `negative` is `(not X)` for a composite goal or non-Boolean
    /// equality that the closure and facts already prove (`goal.rs`).
    NegatedGoal { negative: usize },
}

mod diagnostic;
enum FinalGroundCheck {
    Stopped,
    CustodyRefused,
    NoConflict,
    Conflict(ClosureConflict),
}

mod early_memory;

impl Executor {
    /// The replacement-cascade member: rebuild a ground refutation over the
    /// raw authored roots; see the module documentation. Runs only on a proof
    /// that is not publishable (the strict checker rejects it, or its Alethe
    /// spelling has a known wire gap) and does not rest on a preprocessor
    /// fold to `false` (the fold rescues own that one and call
    /// [`Self::rescue_fold_with_raw_ground_closure`] last). Every failure
    /// leaves `proof` exactly as it was.
    pub(super) fn replace_with_raw_authored_ground_closure_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.authored_cascade_publishable(proof)
            || false_source::rests_on_unattributed_false(self, proof)
        {
            return;
        }
        let _ = self.rebuild_raw_ground_closure(proof);
    }

    /// The last fold-to-`false` rescue; returns whether it committed.
    pub(super) fn rescue_fold_with_raw_ground_closure(&mut self, proof: &mut Proof) -> bool {
        self.rebuild_raw_ground_closure(proof)
    }

    /// Search, emit and commit a wire-a downstream checker candidate; returns whether
    /// `proof` was replaced.
    fn rebuild_raw_ground_closure(&mut self, proof: &mut Proof) -> bool {
        let Some(roots) = self.ground_closure_roots() else {
            closure_note(|| "no raw roots".to_string());
            return false;
        };
        self.rebuild_raw_ground_closure_from(proof, &roots)
    }

    /// [`Self::rebuild_raw_ground_closure`] over roots already re-interned
    /// (raw interning a deep authored conjunction is the expensive part of a
    /// decline, so a caller that has them does not pay it twice).
    fn rebuild_raw_ground_closure_from(&mut self, proof: &mut Proof, roots: &GroundRoots) -> bool {
        let foralls = self.flat_ground_closure_foralls();
        if foralls.iter().any(|f| f.native.is_some())
            && self
                .charge_native_universal(
                    MAX_NODES * MAX_NODES + MAX_ROUNDS * MAX_EDGES,
                    MAX_NODES * 256 + MAX_EDGES * 128,
                )
                .is_none()
        {
            return false;
        }
        let mut search = GroundSearch::default();
        let Some(conflict) = self.saturate_ground_search(&mut search, &roots.search, &foralls)
        else {
            closure_note(|| {
                format!(
                    "no conflict: nodes={} edges={} facts={}",
                    search.closure.nodes().len(),
                    search.closure.edges().len(),
                    search.facts.facts().len()
                )
            });
            return false;
        };
        if foralls.iter().any(|f| f.native.is_some())
            && self.reserve_native_ground_emission(&search).is_none()
        {
            return false;
        }
        let Some(candidate) = self.emit_ground_closure_refutation(&search, conflict.clone()) else {
            closure_note(|| format!("emission declined for {conflict:?}"));
            return false;
        };
        if foralls
            .iter()
            .filter_map(|f| f.native.as_ref())
            .any(|scope| !scope.is_current(self))
        {
            return false;
        }
        let steps = candidate.steps.len();
        let committed = self.commit_raw_ground_closure(proof, candidate, &roots.raw);
        closure_note(|| {
            format!(
                "{} a {steps}-step candidate for {conflict:?} (nodes={} edges={})",
                if committed { "committed" } else { "refused" },
                search.closure.nodes().len(),
                search.closure.edges().len()
            )
        });
        committed
    }

    /// Saturate the closure and the facts over it, returning the first
    /// conflict, or `None` when nothing is refuted within the work bounds.
    fn saturate_ground_search(
        &mut self,
        search: &mut GroundSearch,
        roots: &[TermId],
        foralls: &[FlatForall],
    ) -> Option<ClosureConflict> {
        let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
        self.saturate_ground_search_with_work(search, roots, foralls, &mut work)
    }

    fn saturate_ground_search_with_work(
        &mut self,
        search: &mut GroundSearch,
        roots: &[TermId],
        foralls: &[FlatForall],
        congruence_budget: &mut SharedGroundWork,
    ) -> Option<ClosureConflict> {
        if congruence_budget.refused() {
            return None;
        }
        let mut phase = "seed-closure";
        let mut round = 0;
        let mut disposition = "phase-refusal";
        let mut slice_budget = slice::slice_identity_budget();
        let result = (|| {
            let disequalities = self.seed_ground_closure(&mut search.closure, roots)?;
            phase = "seed-facts";
            self.seed_ground_root_facts(search, roots)?;
            self.seed_authored_ground_clauses(search)?;
            phase = "seed-goals";
            self.seed_ground_goal_terms(search)?;
            phase = "seed-instances";
            self.seed_ground_instances(search, foralls)?;
            let mut offered = 0;
            // One stop for the search (`make_proof_assembly_should_stop`),
            // polled per round.
            let stop = self.make_proof_assembly_should_stop();
            // A typed work refusal reaches the SAME once-at-end check as a
            // stable/round-limit exit. Other refusal/custody paths stay closed.
            macro_rules! phase {
                ($name:literal, $call:expr) => {
                    phase = $name;
                    if $call.is_none() {
                        if congruence_budget.refused() {
                            disposition = "shared-work-refusal";
                            break;
                        }
                        return None;
                    }
                };
            }
            for round_index in 0..MAX_ROUNDS {
                round = round_index + 1;
                phase!(
                    "negative-boolean-facts",
                    self.expand_ground_negative_boolean_facts(search, congruence_budget)
                );
                phase = "evaluation";
                let fresh = search.closure.nodes().get(offered..)?.to_vec();
                offered = search.closure.nodes().len();
                let mut probes = search.probes;
                self.add_ground_evaluation_edges(&mut search.closure, &fresh, &mut probes);
                search.probes = probes;
                if let Some(conflict) =
                    self.ground_closure_conflict(&search.closure, &disequalities)
                {
                    disposition = "conflict";
                    return Some(conflict);
                }
                if let Some(conflict) =
                    self.negated_goal_conflict(search, goal::GoalPhase::Saturating)
                {
                    disposition = "conflict";
                    return Some(conflict);
                }
                if stop() {
                    disposition = "stopped";
                    return None;
                }
                let before = (
                    search.closure.nodes().len(),
                    search.closure.edges().len(),
                    search.facts.facts().len(),
                );
                phase!(
                    "congruence-row",
                    self.ground_closure_round(&mut search.closure, congruence_budget)
                );
                phase!(
                    "offset",
                    self.add_ground_modular_offset_identity_edges(
                        &mut search.closure,
                        &mut slice_budget,
                        congruence_budget
                    )
                );
                phase!(
                    "slice",
                    self.add_ground_slice_identity_edges(&mut search.closure, &mut slice_budget)
                );
                phase!(
                    "read-chain",
                    self.add_ground_read_chain_edges(
                        &mut search.closure,
                        &mut search.read_chains,
                        &search.facts,
                        congruence_budget
                    )
                );
                phase!(
                    "packing",
                    self.add_ground_packing_edges(
                        &mut search.closure,
                        &mut search.packings,
                        &mut slice_budget,
                        congruence_budget
                    )
                );
                phase = "literal-facts";
                if let Some(conflict) = self.derive_ground_literal_facts(search)? {
                    disposition = "conflict";
                    return Some(conflict);
                }
                phase = "instances";
                if let Some(conflict) = self.propagate_ground_instances(search)? {
                    disposition = "conflict";
                    return Some(conflict);
                }
                let after = (
                    search.closure.nodes().len(),
                    search.closure.edges().len(),
                    search.facts.facts().len(),
                );
                if after == before {
                    disposition = "stable-no-conflict";
                    break;
                }
            }
            phase = "final-conflict";
            let conflict = match self.ground_search_final_conflict(
                search,
                &disequalities,
                congruence_budget,
                &stop,
            ) {
                FinalGroundCheck::Stopped => {
                    disposition = "stopped";
                    return None;
                }
                FinalGroundCheck::CustodyRefused => {
                    disposition = "custody-refusal";
                    return None;
                }
                FinalGroundCheck::NoConflict => None,
                FinalGroundCheck::Conflict(conflict) => Some(conflict),
            };
            if conflict.is_some() {
                disposition = if congruence_budget.refused() {
                    "budget-prefix-conflict"
                } else {
                    "conflict"
                };
            } else if congruence_budget.refused() {
                disposition = "shared-work-no-conflict";
            } else if disposition != "stable-no-conflict" {
                disposition = "round-limit";
            }
            conflict
        })();
        crate::executor::unsat_cert::probe_cert_reject(|| {
            self.ground_terminal_probe(
                search,
                phase,
                disposition,
                round,
                slice_budget,
                congruence_budget.remaining(),
            )
        });
        result
    }

    fn ground_search_final_conflict(
        &self,
        search: &GroundSearch,
        disequalities: &[ClosureConflict],
        work: &SharedGroundWork,
        stop: &dyn Fn() -> bool,
    ) -> FinalGroundCheck {
        // This is the inherited once-at-end judgement, not another round or
        // search allowance. It cannot ignore cancellation or retired custody.
        if stop() {
            return FinalGroundCheck::Stopped;
        }
        if work.refused()
            && (!search.read_chains.current_or_unbound(&self.ctx)
                || !search.packings.current_or_unbound(&self.ctx))
        {
            return FinalGroundCheck::CustodyRefused;
        }
        match self
            .ground_closure_conflict(&search.closure, disequalities)
            .or_else(|| self.negated_goal_conflict(search, goal::GoalPhase::Final))
        {
            Some(conflict) => FinalGroundCheck::Conflict(conflict),
            None => FinalGroundCheck::NoConflict,
        }
    }

    /// The raw re-interns of the parsed top-level assertions, then the
    /// elaborated twins of the record shapes in the module documentation.
    /// The parsed assertions are the retained proof surface, or, in a session
    /// that retains none but still certifies (`ay --incremental`), the
    /// definitional pass's copy of the same stack
    /// (`Context::raw_reinternable_parsed_assertions`); without it that
    /// session found no roots, and the pure bit-vector query whose one-shot
    /// proof this lane finds in 0.1 s went to the bit-level members and ran
    /// out its 30 s timeout. An
    /// assertion that uses a source macro (whose expansion would not print as
    /// authored) is not available to this lane at all; one raw interning
    /// refuses (a binder, an over-budget tree, a field read) contributes only
    /// a twin that the exact concrete authored scope holds, that reads a
    /// record field, and that contains no binder. Native placeholder rows use
    /// their exact, aligned concrete source term and never enter the raw
    /// premise ledger. Repeated native rows have a separate finite row bound.
    fn ground_closure_roots(&mut self) -> Option<GroundRoots> {
        let parsed = self.ctx.raw_reinternable_parsed_assertions();
        if parsed.is_empty() || parsed.len() > MAX_NATIVE_AUTHORED_ROWS {
            return None;
        }
        let parsed: Vec<FrontendTerm> = parsed.to_vec();
        let scope = self.exact_concrete_authored_scope();
        let native = self.native_ground_closure_roots(&parsed, &scope)?;
        let fields = self.ctx.dt_field_surface_overrides();
        let mut roots = GroundRoots::default();
        let mut twins = Vec::new();
        for assertion in &parsed {
            if native_roots::is_native_row(assertion) || self.mentions_source_macro(assertion) {
                continue;
            }
            let raw = self.raw_intern_surface(assertion);
            if let Some(root) = raw {
                if !roots.raw.contains(&root) {
                    roots.raw.push(root);
                }
            }
            if raw.is_some_and(|root| !is_record_constant_equality(&self.ctx.terms, root, &fields))
            {
                continue;
            }
            let surface =
                crate::executor::proof_surface_syntax::strip_frontend_annotations(assertion);
            if let Some(twin) = self.ctx.elaborate_surface_subterm(surface) {
                if scope.contains(&twin)
                    && is_binder_free_record_read(&self.ctx.terms, twin, &fields)
                {
                    twins.push(twin);
                }
            }
        }
        roots.search = roots.raw.clone();
        for twin in twins.into_iter().chain(native) {
            if !roots.search.contains(&twin) {
                roots.search.push(twin);
            }
        }
        // A native false universal over an actual registered constructor can
        // refute a query with no ground source row. The receipt, not an empty
        // working-stack guess, licenses the later exact forall_inst premise.
        let native_universal = roots.search.is_empty()
            && super::native_universal_lineage::NativeUniversalSource::capture(self).is_some_and(
                |source| {
                    source
                        .roots()
                        .iter()
                        .any(|&root| matches!(self.ctx.terms.get(root), TermData::Forall(..)))
                },
            );
        (!roots.search.is_empty() || native_universal).then_some(roots)
    }

    /// Admit the candidate's raw roots and commit it, but only after its
    /// derivation checks strictly with no trust step. The roots are raw
    /// re-interns of PARSED top-level assertions, so admitting them grants
    /// nothing the problem did not author; admitting them only for a checked
    /// refutation keeps the premise ledgers free of roots no proof uses.
    ///
    /// Only the raw roots widen the premise scope the commit gate checks
    /// reachable assumes against; a twin or a universal must already be in
    /// the exact concrete authored scope, so that check stays a real one.
    ///
    /// The wire screen runs on the COMMITTED state: the commit purges the
    /// authored respellings of every term the candidate prints (an elaborated
    /// base read the problem spelled as a folded store read, say), and the
    /// screen must judge the spellings the exporter will actually use, after
    /// the presentation passes (`screen.rs`). A candidate whose published
    /// document has a `hole` or `trust` step, or does not render, is reverted
    /// to the exact incumbent proof and overrides. Any failure also restores
    /// both premise ledgers, so no raw root outlives a refutation that was not
    /// kept.
    fn commit_raw_ground_closure(
        &mut self,
        proof: &mut Proof,
        candidate: Proof,
        raw_roots: &[TermId],
    ) -> bool {
        if !Self::proof_derives_empty_clause(&candidate) {
            closure_note(|| "the candidate does not derive the empty clause".to_string());
            return false;
        }
        match self.check_proof_strict_derivation_with_datatypes(&candidate) {
            Ok(quality) if quality.is_complete() => {}
            Ok(_) => {
                closure_note(|| "the candidate's strict replay is incomplete".to_string());
                return false;
            }
            Err(error) => {
                closure_note(|| format!("strict replay refused the candidate: {error}"));
                return false;
            }
        }
        let ledgers = (
            self.last_proof_rebuild_originals.clone(),
            self.last_proof_raw_original_assertions.clone(),
        );
        let mut scope = self.exact_concrete_authored_scope();
        for step in &candidate.steps {
            // Only raw re-interns of parsed assertions enter the raw ledger;
            // a universal is assumed through its concrete authored root,
            // which the scope already holds.
            if let ProofStep::Assume(root) = step {
                if raw_roots.contains(root) {
                    self.record_raw_authored_problem_assertion(*root);
                    if !scope.contains(root) {
                        scope.push(*root);
                    }
                }
            }
        }
        let incumbent = (proof.clone(), self.last_proof_term_overrides.clone());
        let committed = self.commit_if_strictly_checked(proof, candidate, &scope);
        if committed && self.presents_wire_clean(proof) {
            return true;
        }
        closure_note(|| {
            if committed {
                "the published document is not wire-clean".to_string()
            } else {
                "the scoped commit gate refused the candidate".to_string()
            }
        });
        if committed {
            (*proof, self.last_proof_term_overrides) = incumbent;
        }
        (
            self.last_proof_rebuild_originals,
            self.last_proof_raw_original_assertions,
        ) = ledgers;
        false
    }
}
