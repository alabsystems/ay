// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive a premiseless `trust` leaf whose clause **is** a nested
//! `and`-CONJUNCT of an AUTHORED assertion.
//!
//! # The class, as measured
//!
//! The SMT-LIB parser expands `(assert (distinct i0 … i9))` into a single
//! authored `(and (not (= i0 i1)) (not (= i0 i2)) … )`, and the solver then
//! asserts the individual pairwise disequalities. Each of those is a live
//! consequence of an authored assertion, but it is not itself on the
//! `proof_exportable_assertions` whitelist, so
//! `demote_non_problem_assumptions` stamps it a premiseless `trust` step and
//! the mandatory strict check refuses the whole proof.
//!
//! Measured over all 639 `.smt2` under `benchmarks/`
//! (`AY_CENSUS=1 ay solve --no-proof -T:10`, one process per file, 30 s wall),
//! by an INDEPENDENT re-parse of the dumped canonical S-expressions that
//! enumerates every nested `and`-conjunct of every assertion in
//! `complete_problem_assertions_for_strict_proof` and asks whether a leaf's
//! unit clause is one of them **verbatim** — 14 leaves in 5 files, every one
//! at nesting DEPTH 1:
//!
//! | steps | file | shape |
//! |---|---|---|
//! | 9 | `QF_AX/storecomm_t1_np_sf_ai_00010` | `(not (= i0 iN))`, the `distinct` expansion |
//! | 2 | `soundness_qf_uf_incremental/traffic_uflia_falsesat_full` | `not[___z3z___#1]`, `or#2` |
//! | 1 | `QF_AX/storecomm_t1_np_sf_ai_00003` | the same `distinct` expansion |
//! | 1 | `soundness_qf_uf_incremental/traffic_uflia_falsesat_min` | `not[___z3z___#1]` |
//! | 1 | `QF_ALIA/smtlib_regression/pointer-safe-5` | `(not (<= x_7 0))` |
//!
//! # The same class OFF the in-tree corpus (#conjunct-leaf-cap-bail)
//!
//! That in-tree population is 14 leaves because the in-tree corpus ships many
//! small `(assert …)` commands. SMT-LIB ships ONE
//! `(assert (let … (and (and …))))`, and the 2026-08-24 SMT-LIB census
//! (the development design notes) measured **21,029 of
//! 38,037 classified premiseless `Trust` leaves — 55%** to be exactly this
//! shape. The lane was NOT reaching them, and the reason was not a guard:
//! `MAX_CONJUNCT_LEAVES` bounded the leaf POPULATION rather than the lane's
//! own work, so a proof carrying more leaves than the cap derived NOTHING.
//! See that constant, and `MAX_CONJUNCT_ROOT_WORK` for the second bound the
//! same measurement forced. the development design notes
//! has the before/after on both corpora.
//!
//! Note the shapes: NOT ONE of them is a binary `=`, so neither the
//! rewritten-assertion bridge (whose goal must be an equality) nor its
//! non-equality sibling (which needs a congruence between two DIFFERENT
//! terms) can take them. The conjunct is not a rewrite of anything — it is
//! literally a sub-term of the authored assertion, and what it needs is
//! `and_pos`, not congruence.
//!
//! # What replaces the leaf
//!
//! ```text
//!  before                                  after
//!  i: (cl conjunct)  :rule trust           i+0    assume ROOT
//!                                          i+1    (cl (not ROOT) child)  and_pos
//!                                          i+2    (cl child)             th_resolution
//!                                          …      one pair per nesting level
//!                                          i+n:   (cl conjunct)
//! ```
//!
//! The LAST step's clause is byte-identical to the `trust` step's, so every
//! downstream premise reference, resolution and pivot sees exactly the clause
//! it saw before. The emitter is the rewritten-assertion bridge's OWN
//! [`super::rewritten_assertion_bridge::HypothesisLeaf::Conjunct`] arm,
//! reused verbatim rather than re-derived here.
//!
//! # Why NOT `derive_conjunct_assumptions_from_problem_roots`
//!
//! That pass reaches the same class and is DELIBERATELY excluded from the
//! retention-off subset the mandatory-certificate regime uses.
//! `executor/proof_rewrite.rs` records the measurement in full. Note the
//! recorded `+301/−12`, the "8 losses all `QF_IDL/parity`" and the malformed
//! `and_pos` correctness defect are all REFUTED —
//! the development design notes re-derives the
//! whole arm on top of THIS lane's cap fix at +11/−7, 0 malformed `and_pos` in
//! 2,215 files, and 0 `QF_IDL/parity` flips. What survives is two real losses
//! (`QF_LRA/miplib/danoint-50`, `QF_LIA/convert/convert-jpg2gif-query-1141`),
//! which is why the exclusion stands. On the shared population the two lanes
//! are interchangeable: they emit BYTE-IDENTICAL fragments, and on
//! `hard10.smt2` both land on `trust=148`. This lane restructures nothing: it
//! rewrites premiseless
//! argument-free `trust` LEAVES in place and closes every fragment into a
//! self-contained refutation that the UNTOUCHED `check_proof_strict` replays
//! before it may be committed.
//!
//! # Authority
//!
//! The only term this lane assumes is the ROOT, and a root enters the index
//! only when it is in the INTERSECTION of the scope this rewrite was handed
//! and the scope the strict presentation checks against — the sibling lanes'
//! Guard 3, reused verbatim. The CONJUNCT itself is never assumed:
//! `validate_problem_assumptions` would admit an `and`-conjunct assume but
//! `validate_reachable_assumes_in_problem_scope` admits only EXACT
//! membership, so an assumed conjunct is an authority the strict presentation
//! would have to take on faith. Every other step is a premise-free tautology
//! the checker decides from the clause structure alone (`and_pos`) or a
//! resolution decided from its premises (`th_resolution`).
//!
//! # Guards
//!
//! Each is mutation-checked in `authored_conjunct_leaf_tests.rs`
//! (`GUARD_MUTATION_LEDGER` there).
//!
//! 1. **No `Anchor` steps** — their forward references the in-order remap
//!    cannot resolve.
//! 2. **A premiseless, argument-free `trust` step with a unit clause.**
//! 3. **The ROOT is in BOTH authored scopes**, and the leaf's atom is a
//!    conjunct at nesting depth >= 1 — the root itself is never a candidate.
//! 4. **The fragment ends on exactly the leaf's clause**, byte for byte.
//! 5. **The fragment RENDERS** under the export's own surface overrides.
//! 6. **The fragment, CLOSED over the negation of its own conclusion,
//!    strict-checks** — the untouched `check_proof_strict`, run before any
//!    step may enter the proof.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId};

use super::super::Executor;
use super::rewritten_assertion_bridge::{ConjunctDescent, HypothesisLeaf};

/// Largest number of `trust` leaves one call will PLAN A FRAGMENT for.
///
/// # This bounds the WORK, not the population (#conjunct-leaf-cap-bail)
///
/// It used to bound the population: a proof carrying MORE premiseless
/// unit-clause `trust` leaves than this made the whole lane `return 0`, so a
/// proof with 513 leaves derived NOTHING while a proof with 512 derived
/// everything it could. That is the measured reason this lane does not reach
/// the SMT-LIB conjunct class. On
/// `QF_UFLIA/mathsat/EufLaArithmetic/hard/hard10.smt2` — one
/// `(assert (let … (and …)))` that parses to a flat 146-ary `and` — the lane
/// is handed 513 leaves, bails, and abandons 145 authored conjuncts it can
/// derive from the file's own assertion. Bounding the PLANNED count instead
/// changes no ceiling: 512 planned fragments was always reachable, and a leaf
/// the index declines costs one hash lookup, which is why capping the input
/// bought nothing that capping the output does not.
const MAX_CONJUNCT_LEAVES: usize = 512;

/// Deepest `and` nesting the index will descend. Mirrors the sibling lane's
/// bound; the measured population is depth 1 in all 14 instances.
const MAX_CONJUNCT_DEPTH: usize = 64;

/// Largest number of `and` nodes one root's descent will visit. An adversarial
/// problem must not be able to make the walk unbounded.
const MAX_CONJUNCT_NODES: usize = 4096;

/// Total ROOT WEIGHT one call may spend, in term-DAG nodes.
///
/// # Why a fragment count is not a work bound (#conjunct-root-weight)
///
/// Every fragment this lane plans carries `(cl (not ROOT) child)` — the WHOLE
/// authored root, as a literal — and then pays for it three times: the closed
/// strict replay (Guard 6), the renderability check (Guard 5, which FORMATS
/// the root), and the whole-proof re-check at commit. So one call costs
/// `planned × |ROOT|`, not `planned`, and the two factors are anti-correlated
/// in the corpus: the files with thousands of leaves are exactly the files
/// with one enormous authored `and`.
///
/// Measured, and this bound exists because of it. Lifting the population bail
/// alone (`MAX_CONJUNCT_LEAVES` on the input) LOST 9 decided verdicts on a
/// 2,565-file interleaved A/B while gaining 4, and every loss is this product:
/// `QF_IDL/parity/02.200.graph` (root indexed to 4,095 `and` nodes, 7,454
/// leaves) went **1.07 s `unsat` -> 12.07 s `unknown`**, `QF_LRA/miplib/
/// danoint-50` 1.69 s -> 12.05 s, and three `QF_IDL/mathsat/fischer`
/// instances 2-3 s -> 10-12 s. Charging the root's DAG size per fragment
/// keeps the small-root files this lane exists for — `hard10.smt2`'s 146-ary
/// `and` at 145 fragments — and declines the giant-root files before the
/// product can run away.
const MAX_CONJUNCT_ROOT_WORK: usize = 1 << 16;

/// Number of DISTINCT term-DAG nodes reachable from `term`, saturating at
/// `cap`. Bounded so the charge itself cannot be the expensive thing.
fn dag_weight(terms: &ay_core::TermStore, term: TermId, cap: usize) -> usize {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stack = vec![term];
    while let Some(node) = stack.pop() {
        if !seen.insert(node) {
            continue;
        }
        if seen.len() >= cap {
            return cap;
        }
        match terms.get(node) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    seen.len()
}

/// Whether `step` is a leaf this lane may replace (Guard 2).
fn is_conjunct_candidate(step: &ProofStep) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    (premises.is_empty() && args.is_empty() && clause.len() == 1).then(|| clause[0])
}

/// The arguments of `term` when it is an `and` application.
fn conjunction_children(terms: &ay_core::TermStore, term: TermId) -> Option<Vec<TermId>> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "and" => Some(args.clone()),
        _ => None,
    }
}

impl Executor {
    /// Replace every premiseless `trust` step whose unit clause is a nested
    /// `and`-conjunct of an AUTHORED assertion with an `and_pos` descent from
    /// an `assume` of that assertion. Returns the number of leaves replaced,
    /// which the tests assert on.
    pub(in crate::executor) fn derive_authored_conjunct_leaves(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> usize {
        // Guard 1.
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return 0;
        }
        let leaves: Vec<(usize, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| is_conjunct_candidate(step).map(|atom| (index, atom)))
            .collect();
        if leaves.is_empty() {
            return 0;
        }
        // The weighted budget below governs ONLY the capability this change
        // ADDS. A proof whose leaf population the SHIPPED lane already accepted
        // is planned exactly as it was, so no derivation the shipped lane made
        // can be lost. Measured, not assumed: applying the weighted budget to
        // EVERY call instead cost 2,481 conjunct derivations the shipped lane
        // already made on the QF_LRA matched subset (7,178 -> 4,697) and moved
        // that corpus's premiseless `Trust` the WRONG way, 414 -> 546.
        let beyond_shipped_population = leaves.len() > MAX_CONJUNCT_LEAVES;
        let wanted: DetHashSet<TermId> = leaves.iter().map(|&(_, atom)| atom).collect();
        let index = self.authored_conjunct_index(problem_assertions, &wanted);
        if index.is_empty() {
            return 0;
        }
        let overrides = self.last_proof_term_overrides.clone();
        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        let mut spent = 0usize;
        let mut root_weights: DetHashMap<TermId, usize> = DetHashMap::default();
        for (step, atom) in leaves {
            // The WORK bound: at most `MAX_CONJUNCT_LEAVES` fragments are
            // built, closed, strict-checked and rendered per call, whatever
            // the leaf population is. Everything past it keeps its leaf.
            if planned >= MAX_CONJUNCT_LEAVES {
                break;
            }
            // …and the fragment count alone is not the work: each one carries
            // the whole ROOT as a literal, so the ROOT's DAG size is charged
            // against a second, weighted budget. See `MAX_CONJUNCT_ROOT_WORK`.
            if let (true, Some(HypothesisLeaf::Conjunct { root, .. })) =
                (beyond_shipped_population, index.get(&atom))
            {
                let root = *root;
                let weight = match root_weights.get(&root) {
                    Some(&weight) => weight,
                    None => {
                        let weight =
                            dag_weight(&self.ctx.terms, root, MAX_CONJUNCT_ROOT_WORK.max(1));
                        root_weights.insert(root, weight);
                        weight
                    }
                };
                if spent.saturating_add(weight) > MAX_CONJUNCT_ROOT_WORK {
                    continue;
                }
                spent = spent.saturating_add(weight);
            }
            let Some(leaf) = index.get(&atom) else {
                continue;
            };
            let mut fragment: Vec<ProofStep> = Vec::new();
            let mut root_assumes: DetHashMap<TermId, usize> = DetHashMap::default();
            // The emitter is the sibling bridge's own `Conjunct` arm; it
            // returns the index of the step whose clause is `(cl atom)`.
            let Some(last) =
                self.push_hypothesis_leaf(&mut fragment, &mut root_assumes, leaf, atom)
            else {
                continue;
            };
            // Guard 4: the fragment's LAST step is that step, and its clause
            // is byte-identical to the leaf's.
            if last + 1 != fragment.len() {
                continue;
            }
            match fragment.last() {
                Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [atom] => {}
                _ => continue,
            }
            // Guard 6: the untouched strict checker replays the WHOLE fragment,
            // closed over the negation of its own conclusion, before any step
            // of it may enter the proof.
            let closed = ay_proof::close_congruence_derivation(
                &mut self.ctx.terms,
                &ay_proof::CongruenceDerivation {
                    steps: fragment.clone(),
                    clause: vec![atom],
                },
            );
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
                continue;
            }
            // Guard 5: the PRINTER decides renderability, with the export's own
            // overrides, so producer and exporter cannot drift.
            if self.bridge_fragment_is_unrenderable(&fragment, atom, overrides.as_ref()) {
                continue;
            }
            plans[step] = Some(fragment);
            planned += 1;
        }
        if planned == 0 {
            return 0;
        }
        self.commit_bridge_fragments(proof, plans)
    }

    /// Index every WANTED term that is a nested `and`-conjunct of an AUTHORED
    /// root, with the `and_pos` descent that derives it.
    ///
    /// Guard 3: a root enters only when it is in the INTERSECTION of the scope
    /// this rewrite was handed and the scope the strict presentation checks
    /// against. `wanted` is the leaf-atom set, so the walk only ever records
    /// what a leaf actually asked for.
    fn authored_conjunct_index(
        &mut self,
        problem_assertions: &[TermId],
        wanted: &DetHashSet<TermId>,
    ) -> DetHashMap<TermId, HypothesisLeaf> {
        let strict_scope: DetHashSet<TermId> = self
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .collect();
        let mut index: DetHashMap<TermId, HypothesisLeaf> = DetHashMap::default();
        for &root in problem_assertions {
            if !strict_scope.contains(&root)
                || conjunction_children(&self.ctx.terms, root).is_none()
            {
                continue;
            }
            let mut visited = 0usize;
            let mut stack: Vec<(TermId, Vec<ConjunctDescent>)> = vec![(root, Vec::new())];
            while let Some((node, descents)) = stack.pop() {
                visited += 1;
                if visited > MAX_CONJUNCT_NODES {
                    break;
                }
                let Some(children) = conjunction_children(&self.ctx.terms, node) else {
                    // Guard 3, second half: `descents` is empty exactly when
                    // `node` IS the root, and a root is an authored assertion
                    // that never needed demoting.
                    if descents.is_empty() || !wanted.contains(&node) || index.contains_key(&node) {
                        continue;
                    }
                    index.insert(node, HypothesisLeaf::Conjunct { root, descents });
                    continue;
                };
                // A conjunction can itself be a leaf's atom: record it, and
                // still descend into it.
                if !descents.is_empty() && wanted.contains(&node) && !index.contains_key(&node) {
                    index.insert(
                        node,
                        HypothesisLeaf::Conjunct {
                            root,
                            descents: descents.clone(),
                        },
                    );
                }
                if descents.len() >= MAX_CONJUNCT_DEPTH {
                    continue;
                }
                let not_node = self.ctx.terms.mk_not_raw(node);
                for (position, child) in children.into_iter().enumerate() {
                    let Ok(position) = u32::try_from(position) else {
                        continue;
                    };
                    let mut next = descents.clone();
                    next.push(ConjunctDescent {
                        position,
                        parent: node,
                        not_parent: not_node,
                        child,
                    });
                    stack.push((child, next));
                }
            }
        }
        index
    }
}

#[cfg(test)]
#[path = "authored_conjunct_leaf_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "authored_conjunct_leaf_cap_tests.rs"]
mod cap_tests;

#[cfg(test)]
#[path = "authored_conjunct_leaf_guard_tests.rs"]
mod guard_tests;

#[cfg(test)]
#[path = "authored_conjunct_leaf_negative_tests.rs"]
mod negative_tests;

#[cfg(test)]
#[path = "authored_conjunct_leaf_sweep_tests.rs"]
mod sweep_tests;
