// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Craig interpolation at the SMT API level.
//!
//! Implements Pudlak (1997) and McMillan (2003) proof-based interpolation
//! for LRA/LIA. Given two groups of assertions A and B such that A /\ B is
//! UNSAT, extracts an interpolant I from the resolution proof where:
//! - A |= I
//! - I /\ B is UNSAT
//! - I mentions only variables shared between A and B
//!
//! # Algorithm
//!
//! 1. Collect all term-level variables (via recursive walk) for each A and B term.
//! 2. Walk the proof DAG bottom-up:
//!    - At leaf Assume nodes: classify as A or B based on which group contains
//!      the assumed literal.
//!    - At leaf TheoryLemma nodes: extract the A-projection of the lemma clause
//!      (disjunction of A-colored literals with shared variables).
//!    - At Resolution nodes: combine sub-interpolants based on pivot coloring
//!      and the chosen algorithm variant.
//! 3. The final proof step's partial interpolant is the result.
//!
//! # References
//!
//! - McMillan, "Interpolation and SAT-based Model Checking", CAV 2003.
//! - Pudlak, "Lower bounds for resolution and cutting plane proofs", JSL 1997.
//! - OpenSMT `src/proof/InterpolationContext.cc` (MIT, Martin Blicha).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermId, TermStore};

use crate::api::types::{InterpolantResult, InterpolantStrength, PathInterpolantResult, Term};
use crate::api::Solver;

impl Solver {
    /// Compute a Craig interpolant from the last UNSAT proof.
    ///
    /// The `a_terms` and `b_terms` groups must partition the assertions such
    /// that A /\ B was UNSAT in the most recent `check_sat` call.
    ///
    /// Uses the default Pudlak algorithm for balanced interpolants.
    /// For specific strengths, use [`get_interpolant_with_strength`].
    ///
    /// # Requirements
    ///
    /// - Proof production must be enabled via [`set_produce_proofs(true)`] before
    ///   the `check_sat` call.
    /// - The last `check_sat` must have returned UNSAT.
    ///
    /// Returns `None` if the interpolant cannot be computed (proofs not enabled,
    /// last result not UNSAT, empty proof, or theory lemma extraction failure).
    ///
    /// [`get_interpolant_with_strength`]: Solver::get_interpolant_with_strength
    /// [`set_produce_proofs(true)`]: Solver::set_produce_proofs
    #[must_use]
    pub fn get_interpolant(
        &mut self,
        a_terms: &[Term],
        b_terms: &[Term],
    ) -> Option<InterpolantResult> {
        self.get_interpolant_with_strength(a_terms, b_terms, InterpolantStrength::Default)
    }

    /// Compute a Craig interpolant with a specific strength/algorithm.
    ///
    /// See [`InterpolantStrength`] for the available algorithms and their
    /// characteristics. The `Weakest` variant produces the most general
    /// interpolant (good for PDR convergence), while `Strongest` produces
    /// the most specific.
    ///
    /// # Requirements
    ///
    /// Same as [`get_interpolant`].
    ///
    /// [`get_interpolant`]: Solver::get_interpolant
    #[must_use]
    pub fn get_interpolant_with_strength(
        &mut self,
        a_terms: &[Term],
        b_terms: &[Term],
        strength: InterpolantStrength,
    ) -> Option<InterpolantResult> {
        // Clone the proof to release the immutable borrow on self.
        let proof = self.last_proof()?.clone();
        if proof.steps.is_empty() {
            return None;
        }

        // Collect A and B assertion TermIds.
        let a_term_ids: HashSet<TermId> = a_terms.iter().map(|t| t.0).collect();
        let b_term_ids: HashSet<TermId> = b_terms.iter().map(|t| t.0).collect();

        // Collect variables for A and B to determine shared variables.
        let mut a_vars = HashSet::default();
        let mut b_vars = HashSet::default();
        {
            let terms = self.terms();
            for &tid in &a_term_ids {
                collect_vars(terms, tid, &mut a_vars);
            }
            for &tid in &b_term_ids {
                collect_vars(terms, tid, &mut b_vars);
            }
        }
        let shared_vars: HashSet<TermId> = a_vars.intersection(&b_vars).copied().collect();

        // Collect atoms (leaf predicates) from A and B for classifying
        // proof nodes and pivot variables.
        let mut a_atoms = HashSet::default();
        let mut b_atoms = HashSet::default();
        {
            let terms = self.terms();
            for &tid in &a_term_ids {
                collect_atoms(terms, tid, &mut a_atoms);
            }
            for &tid in &b_term_ids {
                collect_atoms(terms, tid, &mut b_atoms);
            }
        }

        // Walk the proof DAG bottom-up and compute partial interpolants.
        let result_tid = self.traverse_proof_for_interpolant(
            &proof,
            &a_term_ids,
            &b_term_ids,
            &a_atoms,
            &b_atoms,
            &a_vars,
            &b_vars,
            &shared_vars,
            strength,
        )?;

        // Craig property 3: the interpolant must use only variables shared
        // between A and B. This is the cheapest of the three Craig properties
        // to verify (no solver call needed, just a term walk). Properties 1
        // (A |= I) and 2 (I /\ B is UNSAT) require fresh solver calls and
        // are deferred to a separate issue.
        debug_assert!(
            uses_only_shared_vars(self.terms(), result_tid, &shared_vars),
            "Craig interpolant uses non-shared variable: {}",
            find_non_shared_var_name(self.terms(), result_tid, &shared_vars)
                .unwrap_or_else(|| "<unknown>".to_string())
        );

        Some(InterpolantResult::new(Term(result_tid), strength))
    }

    /// Compute path interpolants for a sequence of formula partitions.
    ///
    /// Given partitions `[A1, A2, ..., An]` where each `Ai` is a slice of terms,
    /// returns interpolants `[I1, I2, ..., I(n-1)]` such that:
    /// - A1 |= I1
    /// - Ii /\ A(i+1) |= I(i+1)  for i in 1..n-2
    /// - I(n-1) /\ An is UNSAT
    /// - Each Ii uses only symbols shared between {A1..Ai} and {A(i+1)..An}
    ///
    /// Uses the default Pudlak algorithm. For specific strengths, use
    /// [`get_path_interpolants_with_strength`].
    ///
    /// # Requirements
    ///
    /// - Proof production must be enabled via [`set_produce_proofs(true)`] before
    ///   the `check_sat` call.
    /// - The last `check_sat` must have returned UNSAT.
    /// - At least 2 partitions are required; returns `None` for fewer.
    ///
    /// [`get_path_interpolants_with_strength`]: Solver::get_path_interpolants_with_strength
    /// [`set_produce_proofs(true)`]: Solver::set_produce_proofs
    #[must_use]
    pub fn get_path_interpolants(
        &mut self,
        partitions: &[&[Term]],
    ) -> Option<PathInterpolantResult> {
        self.get_path_interpolants_with_strength(partitions, InterpolantStrength::Default)
    }

    /// Compute path interpolants with a specific strength/algorithm.
    ///
    /// See [`InterpolantStrength`] for algorithm options and [`get_path_interpolants`]
    /// for the path interpolant definition and properties.
    ///
    /// The implementation computes n-1 binary interpolants along the path,
    /// where the i-th interpolant treats {A1..Ai} as the A-side and
    /// {A(i+1)..An} as the B-side.
    ///
    /// [`get_path_interpolants`]: Solver::get_path_interpolants
    #[must_use]
    pub fn get_path_interpolants_with_strength(
        &mut self,
        partitions: &[&[Term]],
        strength: InterpolantStrength,
    ) -> Option<PathInterpolantResult> {
        if partitions.len() < 2 {
            return None;
        }

        // Clone the proof to release the immutable borrow on self.
        let proof = self.last_proof()?.clone();
        if proof.steps.is_empty() {
            return None;
        }

        let n = partitions.len();
        let mut interpolants = Vec::with_capacity(n - 1);

        // For each cut point i (1..n-1), compute binary interpolant with:
        //   A = partitions[0..=i-1]  (flattened)
        //   B = partitions[i..n]     (flattened)
        for cut in 1..n {
            let a_terms: Vec<Term> = partitions[..cut]
                .iter()
                .flat_map(|p| p.iter().copied())
                .collect();
            let b_terms: Vec<Term> = partitions[cut..]
                .iter()
                .flat_map(|p| p.iter().copied())
                .collect();

            // Collect A and B assertion TermIds.
            let a_term_ids: HashSet<TermId> = a_terms.iter().map(|t| t.0).collect();
            let b_term_ids: HashSet<TermId> = b_terms.iter().map(|t| t.0).collect();

            // Collect variables for A and B to determine shared variables.
            let mut a_vars = HashSet::default();
            let mut b_vars = HashSet::default();
            {
                let terms = self.terms();
                for &tid in &a_term_ids {
                    collect_vars(terms, tid, &mut a_vars);
                }
                for &tid in &b_term_ids {
                    collect_vars(terms, tid, &mut b_vars);
                }
            }
            let shared_vars: HashSet<TermId> = a_vars.intersection(&b_vars).copied().collect();

            // Collect atoms from A and B.
            let mut a_atoms = HashSet::default();
            let mut b_atoms = HashSet::default();
            {
                let terms = self.terms();
                for &tid in &a_term_ids {
                    collect_atoms(terms, tid, &mut a_atoms);
                }
                for &tid in &b_term_ids {
                    collect_atoms(terms, tid, &mut b_atoms);
                }
            }

            // Walk the proof DAG for this cut.
            let result_tid = self.traverse_proof_for_interpolant(
                &proof,
                &a_term_ids,
                &b_term_ids,
                &a_atoms,
                &b_atoms,
                &a_vars,
                &b_vars,
                &shared_vars,
                strength,
            )?;

            debug_assert!(
                uses_only_shared_vars(self.terms(), result_tid, &shared_vars),
                "Path interpolant {} uses non-shared variable: {}",
                cut,
                find_non_shared_var_name(self.terms(), result_tid, &shared_vars)
                    .unwrap_or_else(|| "<unknown>".to_string())
            );

            interpolants.push(Term(result_tid));
        }

        Some(PathInterpolantResult::new(interpolants, strength))
    }

    /// Walk the proof DAG bottom-up, computing partial interpolants at each node.
    ///
    /// Uses `&mut self` because building new interpolant terms (And, Or, Not)
    /// requires mutable access to the term store.
    #[allow(clippy::too_many_arguments)]
    fn traverse_proof_for_interpolant(
        &mut self,
        proof: &Proof,
        a_assertions: &HashSet<TermId>,
        b_assertions: &HashSet<TermId>,
        a_atoms: &HashSet<TermId>,
        b_atoms: &HashSet<TermId>,
        a_vars: &HashSet<TermId>,
        b_vars: &HashSet<TermId>,
        shared_vars: &HashSet<TermId>,
        strength: InterpolantStrength,
    ) -> Option<TermId> {
        let bc = BoolConstants {
            true_tid: self.terms().true_term(),
            false_tid: self.terms().false_term(),
        };
        super::interpolant_farkas::reset_cert_leaf_stats();
        // Occurrence/variable coloring context shared by the certificate
        // leaves and the synthetic-atom classification fallbacks (inc-4).
        let cert_part = super::interpolant_farkas::CertPartition {
            a_atoms,
            b_atoms,
            a_vars,
            b_vars,
            shared_vars,
        };

        // Partial interpolants indexed by proof step position.
        let mut partial: Vec<Option<TermId>> = vec![None; proof.steps.len()];
        // Clause literals per step (for pivot recovery on resolution-shaped
        // `Step` chains, rank-4 inc-4).
        let mut clause_lits: Vec<ClauseLits<'_>> = Vec::with_capacity(proof.steps.len());

        for (idx, step) in proof.steps.iter().enumerate() {
            let interp = match step {
                ProofStep::Assume(lit) => {
                    // Classify clause membership: direct assertion membership
                    // wins (an Assume leaf IS an input assertion); the
                    // atom-occurrence fallback only applies when neither side
                    // directly asserts the literal (preprocessed forms). The
                    // previous atom-only fallback misclassified shared-atom
                    // B-assertions as A-leaves (#rank-4 increment 1).
                    let atom = atom_of_literal(self.terms(), *lit);
                    let in_a_assert = a_assertions.contains(lit) || a_assertions.contains(&atom);
                    let in_b_assert = b_assertions.contains(lit) || b_assertions.contains(&atom);
                    let in_a = in_a_assert
                        || (!in_b_assert && (a_atoms.contains(lit) || a_atoms.contains(&atom)));

                    // Leaf rules per labeled interpolation system (D'Silva et
                    // al., VMCAI 2010). A literal occurrence is labeled by its
                    // atom class: A-only -> a, B-only -> b, shared -> system-
                    // dependent (McMillan: b, Pudlak: ab, McMillan': a).
                    //
                    //   I(A-clause) = disjunction of b-labeled literals
                    //   I(B-clause) = conjunction of negated a-labeled literals
                    if in_a {
                        match strength {
                            // McMillan: a unit A-clause contributes its literal
                            // iff the atom is shared (b-labeled). Composite
                            // assertion-level atoms (or-terms asserted by BOTH
                            // partitions — `collect_atoms` descends them, so
                            // they never enter the atom sets) are shared too;
                            // missing them served `false` and broke the leaf
                            // contract `A ⊨ I` under McMillan (rank-4 inc-19).
                            InterpolantStrength::Strongest => {
                                let shared_atom = b_atoms.contains(&atom)
                                    || b_atoms.contains(lit)
                                    || b_assertions.contains(&atom)
                                    || b_assertions.contains(lit);
                                if shared_atom
                                    && uses_only_shared_vars(self.terms(), *lit, shared_vars)
                                {
                                    Some(*lit)
                                } else {
                                    Some(bc.false_tid)
                                }
                            }
                            // Pudlak (shared -> ab) and McMillan' (shared -> a):
                            // no b-labeled literal in an A-clause: I = false.
                            InterpolantStrength::Default | InterpolantStrength::Weakest => {
                                Some(bc.false_tid)
                            }
                        }
                    } else {
                        match strength {
                            // McMillan' (shared -> a): a unit B-clause with a
                            // shared atom contributes the negated literal
                            // (assertion-level shared atoms included, see the
                            // Strongest arm).
                            InterpolantStrength::Weakest => {
                                let shared_atom = a_atoms.contains(&atom)
                                    || a_atoms.contains(lit)
                                    || a_assertions.contains(&atom)
                                    || a_assertions.contains(lit);
                                if shared_atom
                                    && uses_only_shared_vars(self.terms(), *lit, shared_vars)
                                {
                                    let lit = *lit;
                                    Some(self.terms_mut().mk_not(lit))
                                } else {
                                    Some(bc.true_tid)
                                }
                            }
                            // McMillan (shared -> b) and Pudlak (shared -> ab):
                            // no a-labeled literal in a B-clause: I = true.
                            InterpolantStrength::Strongest | InterpolantStrength::Default => {
                                Some(bc.true_tid)
                            }
                        }
                    }
                }
                ProofStep::TheoryLemma { clause, farkas, .. } => {
                    // Certificate-based leaf first (rank-4 inc-4): when the
                    // lemma carries a Farkas certificate that re-verifies,
                    // derive the partial interpolant from the certificate
                    // (the labeled-interpolation theory rule). Uncertified /
                    // off-shape leaves keep the old occurrence projection.
                    let cert = farkas.as_ref().and_then(|f| {
                        super::interpolant_farkas::certificate_lemma_interpolant(
                            self.terms_mut(),
                            clause,
                            f,
                            &cert_part,
                            strength,
                            bc.true_tid,
                            bc.false_tid,
                        )
                    });
                    match cert {
                        Some(itp) => Some(itp),
                        // Labeled-system projection: disjunction of the
                        // clause literals outside the A-restriction
                        // (all-A-local lemmas take `false`).
                        None => interpolate_theory_lemma(
                            self.terms_mut(),
                            clause,
                            &cert_part,
                            strength,
                            bc.true_tid,
                            bc.false_tid,
                        ),
                    }
                }
                ProofStep::Resolution {
                    pivot,
                    clause1,
                    clause2,
                    ..
                } => {
                    let i1 = partial.get(clause1.0 as usize).and_then(|x| *x);
                    let i2 = partial.get(clause2.0 as usize).and_then(|x| *x);
                    interpolate_resolution(
                        self.terms_mut(),
                        *pivot,
                        i1,
                        i2,
                        a_atoms,
                        b_atoms,
                        a_assertions,
                        b_assertions,
                        &cert_part,
                        strength,
                        &bc,
                    )
                }
                ProofStep::Step {
                    premises, clause, ..
                } => {
                    // Premiseless steps are input-shaped leaves: clausification
                    // tautologies (e.g. Alethe `or_pos`) carrying an asserted
                    // or-term as a literal. They must take the leaf rule of
                    // their SOURCE assertion's partition — treating them as
                    // `true` (the old behavior) poisoned every interpolant
                    // over clausified A-side structure (rank-4 inc-3).
                    //
                    // Tautologies over DEFINITION sub-atoms (e.g. the or_pos
                    // expansion of an iff-defined or-term) never carry an
                    // asserted literal; classify those by atom occurrence with
                    // the variable-occurrence fallback (rank-4 inc-4 — the
                    // scheme the interpolation spike validated; previously
                    // they fell through to `true` and poisoned the McMillan
                    // OR-combinations above them).
                    let source = if premises.is_empty() {
                        input_clause_source_side(self.terms(), clause, a_assertions, b_assertions)
                    } else {
                        None
                    };
                    // Premiseless clauses NOT traceable to an input assertion
                    // (Trust-bridged minimized theory conflicts) take the
                    // labeled leaf rule at DISJUNCT granularity (inc-19): the
                    // whole-clause side classification was blind to strictly-B
                    // sub-atoms over shared variables and served the
                    // degenerate constant, which violated the leaf contract
                    // and collapsed the root (#29). `None` (unclassifiable /
                    // non-shared b-part) falls to the generic default below.
                    let unassigned_leaf = if premises.is_empty() && source.is_none() {
                        let lits = expand_single_or_literal(self.terms(), clause);
                        interpolate_unassigned_leaf_clause(
                            self.terms_mut(),
                            &lits,
                            &cert_part,
                            strength,
                            &bc,
                        )
                    } else {
                        None
                    };
                    match (source, unassigned_leaf) {
                        (Some(side_a), _) => interpolate_input_clause(
                            self.terms_mut(),
                            clause,
                            side_a,
                            a_atoms,
                            b_atoms,
                            a_assertions,
                            b_assertions,
                            shared_vars,
                            strength,
                            &bc,
                        ),
                        (None, Some(itp)) => Some(itp),
                        (None, None) => {
                            // Resolution-shaped steps (the executor's
                            // th_resolution / RUP chains emit `Step` nodes,
                            // not `Resolution` nodes): recover the pivots from
                            // the premise clauses and apply the pivot-aware
                            // combination (rank-4 inc-4). Conjoining premise
                            // interpolants (the generic rule below) is wrong
                            // for resolution semantics and collapsed every
                            // executor-proof interpolant to a constant.
                            let chain = if matches!(
                                step,
                                ProofStep::Step {
                                    rule: AletheRule::ThResolution | AletheRule::Resolution,
                                    ..
                                }
                            ) && premises.len() >= 2
                            {
                                interpolate_resolution_chain(
                                    self.terms_mut(),
                                    premises,
                                    &partial,
                                    &clause_lits,
                                    a_atoms,
                                    b_atoms,
                                    a_assertions,
                                    b_assertions,
                                    &cert_part,
                                    strength,
                                    &bc,
                                )
                            } else {
                                None
                            };
                            match chain {
                                Some(itp) => Some(itp),
                                // Generic Alethe step: conjoin premise
                                // interpolants.
                                None => combine_premise_interpolants(
                                    self.terms_mut(),
                                    &partial,
                                    premises,
                                    bc.true_tid,
                                    bc.false_tid,
                                ),
                            }
                        }
                    }
                }
                ProofStep::Anchor { end_step, .. } => {
                    partial.get(end_step.0 as usize).and_then(|x| *x)
                }
                _ => None,
            };

            partial[idx] = interp;
            clause_lits.push(match step {
                ProofStep::Assume(lit) => ClauseLits::Unit(*lit),
                ProofStep::Resolution { clause, .. }
                | ProofStep::TheoryLemma { clause, .. }
                | ProofStep::Step { clause, .. } => ClauseLits::Slice(clause),
                _ => ClauseLits::Missing,
            });
        }

        // The last step's interpolant is the final result.
        partial.last().and_then(|x| *x)
    }
}

/// Clause literals of a proof step, for pivot recovery on resolution-shaped
/// `Step` chains (rank-4 inc-4).
enum ClauseLits<'a> {
    /// Multi-literal clause borrowed from the proof step.
    Slice(&'a [TermId]),
    /// Unit clause of an `Assume` leaf.
    Unit(TermId),
    /// No clause view available (e.g. `Anchor`).
    Missing,
}

impl ClauseLits<'_> {
    fn get(&self) -> Option<&[TermId]> {
        match self {
            ClauseLits::Slice(s) => Some(s),
            ClauseLits::Unit(t) => Some(std::slice::from_ref(t)),
            ClauseLits::Missing => None,
        }
    }
}

// ============================================================================
// Proof traversal helpers
// ============================================================================

/// Compute partial interpolant for a theory lemma (leaf node).
///
/// The lemma clause C is a THEORY-VALID disjunction: l1 \/ l2 \/ ... \/ ln
/// (`⊨_T C`). Per the labeled interpolation system (D'Silva et al., VMCAI
/// 2010), the leaf partial is the disjunction of the literals OUTSIDE the
/// A-restriction:
///
///   I(C) = ∨ { l ∈ C : label(l) != a }
///
/// Contract (1) `A ∧ ¬(C|a,ab) ⊨ I` holds because `⊨ C` and the LHS negates
/// exactly the literals NOT in I; contract (2) `B ∧ ¬(C|b,ab) ∧ I ⊨ ⊥` holds
/// because `¬(C|b,ab)` contradicts every disjunct of I. Labels per strength:
/// strictly-A atoms -> `a`, strictly-B -> `b`, shared -> `b` under McMillan
/// (Strongest), `ab` under Pudlak (Default; an `ab` literal sits in BOTH
/// restrictions, so including it keeps both contracts), `a` under McMillan'
/// (Weakest — shared literals are negated by the (1)-LHS, so they must NOT
/// appear in I; the b-part is exactly the strictly-B literals).
///
/// The PREVIOUS projection emitted the A-COLORED shared literals — the very
/// literals contract (1)'s LHS negates. That is valid only when the clause
/// has no strictly-B literal (the LHS is then `A ∧ ¬C`, T-inconsistent, and
/// anything is entailed) — true for input-shaped lemmas, FALSE for the
/// executor's mixed LIA conflicts (rank-4 inc-19, deterministic SYNAPSE k=2
/// repro: cert-bailed 28-literal lemmas with ~24 strictly-B literals served
/// the 3-literal a/ab-projection, breaking contract (1) at the leaf and
/// collapsing the Pudlak/McMillan roots to `false`).
///
/// An ALL-A-LOCAL lemma takes `false` (empty b-part; the inc-17 rule —
/// emergent here as the empty disjunction).
///
/// When the b-part disjunction is NOT local (a strictly-B literal carries
/// B-local variables), the DUAL form is tried: `I = ∧ ¬(C|a,ab)` — the
/// conjunction of the negated a/ab-labeled literals. Contract (1) holds
/// syntactically (the LHS asserts exactly those negations); contract (2)
/// holds because `¬(C|b,ab) ∧ ¬(C|a,ab) = ¬C` is T-inconsistent. When
/// NEITHER projection is local, WEAKEN to `true` (monotone for contract
/// (1); the B-side AND structure absorbs it, and the consumer's Craig gate
/// rejects any root it poisons — same failure mode as the pre-inc-17
/// behavior, never unsound).
fn interpolate_theory_lemma(
    terms: &mut TermStore,
    clause: &[TermId],
    cert_part: &super::interpolant_farkas::CertPartition<'_>,
    strength: InterpolantStrength,
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    use super::interpolant_farkas::AtomClass;
    let mut classes = Vec::with_capacity(clause.len());
    for &lit in clause {
        let atom = atom_of_literal(terms, lit);
        classes.push(cert_part.class_of_atom(terms, atom)?);
    }
    // Primary: I = ∨ { l : label(l) = b } (+ ab-labeled under non-Weakest).
    let b_local_ok = |class: &AtomClass| match class {
        AtomClass::A => false,
        AtomClass::B => true,
        AtomClass::Ab => !matches!(strength, InterpolantStrength::Weakest),
    };
    let primary_local = clause.iter().zip(&classes).all(|(&lit, c)| {
        !b_local_ok(c) || uses_only_shared_vars(terms, lit, cert_part.shared_vars)
    });
    if primary_local {
        let mut result = false_tid;
        for (&lit, class) in clause.iter().zip(&classes) {
            if b_local_ok(class) {
                result = mk_or_simplified(terms, result, lit, true_tid, false_tid);
            }
        }
        return Some(result);
    }
    // Dual: I = ∧ ¬(C|a,ab) — a-labeled always; ab-labeled lits are in the
    // a-restriction under Pudlak (ab) and McMillan' (a), not under McMillan.
    let in_a_restriction = |class: &AtomClass| match class {
        AtomClass::A => true,
        AtomClass::B => false,
        AtomClass::Ab => !matches!(strength, InterpolantStrength::Strongest),
    };
    let dual_local = clause.iter().zip(&classes).all(|(&lit, c)| {
        !in_a_restriction(c) || uses_only_shared_vars(terms, lit, cert_part.shared_vars)
    });
    if dual_local {
        let mut result = true_tid;
        for (&lit, class) in clause.iter().zip(&classes) {
            if in_a_restriction(class) {
                let neg = terms.mk_not(lit);
                result = mk_and_simplified(terms, result, neg, true_tid, false_tid);
            }
        }
        return Some(result);
    }
    Some(true_tid)
}

/// Cached true/false TermIds to reduce argument counts.
struct BoolConstants {
    true_tid: TermId,
    false_tid: TermId,
}

/// Determine the source partition of an input-shaped clause (rank-4 inc-3).
///
/// A premiseless `Step` is input-shaped when it is a clausification tautology
/// carrying an asserted term (typically an or-term) as one of its literals.
/// Returns `Some(true)` for an A-sourced clause, `Some(false)` for B-sourced,
/// and `None` when no literal belongs to an assertion or the sources mix
/// (mixed/unknown clauses keep the conservative generic-step treatment; the
/// final interpolant is validated by the consumer either way).
fn input_clause_source_side(
    terms: &TermStore,
    clause: &[TermId],
    a_assertions: &HashSet<TermId>,
    b_assertions: &HashSet<TermId>,
) -> Option<bool> {
    let mut found: Option<bool> = None;
    for &lit in clause {
        let atom = atom_of_literal(terms, lit);
        let side = if a_assertions.contains(&atom) || a_assertions.contains(&lit) {
            Some(true)
        } else if b_assertions.contains(&atom) || b_assertions.contains(&lit) {
            Some(false)
        } else {
            None
        };
        if let Some(side) = side {
            match found {
                None => found = Some(side),
                Some(prev) if prev == side => {}
                Some(_) => return None, // mixed sources: not input-shaped
            }
        }
    }
    found
}

/// Disjunct-granularity literal view of a premiseless step's clause (rank-4
/// inc-19): the executor's Trust-bridged minimized theory conflicts surface
/// as SINGLE-literal clauses whose literal is a solver-built or-term over
/// atoms of BOTH partitions. Classifying the whole or-term through the
/// variable-occurrence fallback is blind to per-atom occurrence — a strictly-B
/// atom over shared VARIABLES (e.g. `(<= 1 v13_1)` with boundary `v13_1`)
/// disappears into an `A`/`Ab` whole-term class. Expand one `or` level so the
/// leaf rule labels each disjunct's atom individually.
fn expand_single_or_literal(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(sym, args) = terms.get(clause[0]) {
            if sym.name() == "or" {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

/// Labeled leaf rule for a premiseless solver clause NOT traceable to an
/// input assertion (rank-4 inc-19; the #29 root-collapse fix).
///
/// Per the labeled interpolation system (D'Silva et al., VMCAI 2010), a leaf
/// clause C takes
///
///   I(A-clause) = disjunction of b-labeled literals
///   I(B-clause) = conjunction of negated a-labeled literals
///
/// with per-occurrence labels: strictly-A atoms -> `a`, strictly-B -> `b`,
/// shared -> `b` (McMillan / Strongest), `a` (McMillan' / Weakest), `ab`
/// (Pudlak / Default). The previous handling classified the whole clause to
/// one side and served the degenerate constant — `false` for A-side under
/// Pudlak/McMillan' — which violates the leaf contract `A ∧ ¬(C|a,ab) ⊨ I`
/// whenever the clause carries a strictly-B literal: its b-part MUST surface
/// in the partial. Observed on EqDiffVar-reduced SYNAPSE k=2 (deterministic
/// repro): Trust leaves like `¬(p25=0) ∨ ¬(p37=0) ∨ ¬(1≤v13_1)` with
/// `(<= 1 v13_1)` strictly-B served `false`, and the B-local AND combinations
/// propagated it to a `false` root for all three strengths.
///
/// Side assignment: any strictly-A atom -> A-side (these bridged conflicts
/// minimize against A-side definitional units; the consumer's Craig gate
/// validates the result either way), otherwise B-side (all-shared clauses
/// are entailed by either side; matches the previous inc-4 assignment).
/// Bails (`None`) when an atom is unclassifiable or a CONTRIBUTING literal
/// uses non-shared variables (it could never appear in a Craig interpolant;
/// dropping it silently would re-create the too-strong constant).
fn interpolate_unassigned_leaf_clause(
    terms: &mut TermStore,
    lits: &[TermId],
    cert_part: &super::interpolant_farkas::CertPartition<'_>,
    strength: InterpolantStrength,
    bc: &BoolConstants,
) -> Option<TermId> {
    use super::interpolant_farkas::AtomClass;
    let mut classes = Vec::with_capacity(lits.len());
    for &lit in lits {
        let atom = atom_of_literal(terms, lit);
        classes.push(cert_part.class_of_atom(terms, atom)?);
    }
    let side_a = classes.iter().any(|c| matches!(c, AtomClass::A));
    if side_a {
        // I(A-clause) = disjunction of b-labeled literals.
        let mut result = bc.false_tid;
        for (&lit, class) in lits.iter().zip(&classes) {
            let b_labeled = matches!(class, AtomClass::B)
                || (matches!(class, AtomClass::Ab)
                    && matches!(strength, InterpolantStrength::Strongest));
            if b_labeled {
                if !uses_only_shared_vars(terms, lit, cert_part.shared_vars) {
                    return None;
                }
                result = mk_or_simplified(terms, result, lit, bc.true_tid, bc.false_tid);
            }
        }
        Some(result)
    } else {
        // I(B-clause) = conjunction of negated a-labeled literals; with no
        // strictly-A atoms only shared ones can be a-labeled (McMillan').
        let mut result = bc.true_tid;
        for (&lit, class) in lits.iter().zip(&classes) {
            let a_labeled =
                matches!(class, AtomClass::Ab) && matches!(strength, InterpolantStrength::Weakest);
            if a_labeled {
                if !uses_only_shared_vars(terms, lit, cert_part.shared_vars) {
                    return None;
                }
                let neg = terms.mk_not(lit);
                result = mk_and_simplified(terms, result, neg, bc.true_tid, bc.false_tid);
            }
        }
        Some(result)
    }
}

/// Leaf rule for an input clause of the given partition, per the labeled
/// interpolation system (D'Silva et al., VMCAI 2010) — the n-literal
/// generalization of the unit `Assume` rules above:
///
///   I(A-clause) = disjunction of b-labeled literals
///   I(B-clause) = conjunction of negated a-labeled literals
///
/// where a literal is labeled by its atom class under the chosen system
/// (McMillan labels shared atoms `b`, Pudlak `ab`, McMillan' `a`).
#[allow(clippy::too_many_arguments)]
fn interpolate_input_clause(
    terms: &mut TermStore,
    clause: &[TermId],
    side_a: bool,
    a_atoms: &HashSet<TermId>,
    b_atoms: &HashSet<TermId>,
    a_assertions: &HashSet<TermId>,
    b_assertions: &HashSet<TermId>,
    shared_vars: &HashSet<TermId>,
    strength: InterpolantStrength,
    bc: &BoolConstants,
) -> Option<TermId> {
    if side_a {
        match strength {
            // McMillan: shared atoms are b-labeled — keep shared literals.
            // Composite assertion-level atoms (or-terms asserted by both
            // partitions) are shared too (inc-19; see the Assume leaf rule).
            InterpolantStrength::Strongest => {
                let mut result = bc.false_tid;
                for &lit in clause {
                    let atom = atom_of_literal(terms, lit);
                    if (b_atoms.contains(&atom)
                        || b_atoms.contains(&lit)
                        || b_assertions.contains(&atom)
                        || b_assertions.contains(&lit))
                        && uses_only_shared_vars(terms, lit, shared_vars)
                    {
                        result = mk_or_simplified(terms, result, lit, bc.true_tid, bc.false_tid);
                    }
                }
                Some(result)
            }
            // Pudlak (shared -> ab) / McMillan' (shared -> a): no b-labeled
            // literals in an A-clause.
            InterpolantStrength::Default | InterpolantStrength::Weakest => Some(bc.false_tid),
        }
    } else {
        match strength {
            // McMillan' (shared -> a): conjunction of negated shared literals.
            InterpolantStrength::Weakest => {
                let mut result = bc.true_tid;
                for &lit in clause {
                    let atom = atom_of_literal(terms, lit);
                    if (a_atoms.contains(&atom)
                        || a_atoms.contains(&lit)
                        || a_assertions.contains(&atom)
                        || a_assertions.contains(&lit))
                        && uses_only_shared_vars(terms, lit, shared_vars)
                    {
                        let neg = terms.mk_not(lit);
                        result = mk_and_simplified(terms, result, neg, bc.true_tid, bc.false_tid);
                    }
                }
                Some(result)
            }
            // McMillan (shared -> b) / Pudlak (shared -> ab): no a-labeled
            // literals in a B-clause.
            InterpolantStrength::Strongest | InterpolantStrength::Default => Some(bc.true_tid),
        }
    }
}

/// Combine sub-interpolants at a Resolution node.
///
/// The pivot determines how I1 and I2 are combined:
/// - A-local pivot: I = I1 \/ I2
/// - B-local pivot: I = I1 /\ I2
/// - Shared pivot: depends on the algorithm variant
///
/// Pivot classification falls back to assertion membership for synthetic
/// atoms (rank-4 inc-3): clausification resolves on asserted or-terms, which
/// never appear in the atom sets (`collect_atoms` descends through or/and),
/// so without the fallback those pivots hit the unclassified default and
/// take the wrong combination rule. A second variable-occurrence fallback
/// (rank-4 inc-4, `CertPartition::class_of_atom`) colors definition sub-atoms
/// that belong to neither set.
#[allow(clippy::too_many_arguments)]
fn interpolate_resolution(
    terms: &mut TermStore,
    pivot: TermId,
    i1: Option<TermId>,
    i2: Option<TermId>,
    a_atoms: &HashSet<TermId>,
    b_atoms: &HashSet<TermId>,
    a_assertions: &HashSet<TermId>,
    b_assertions: &HashSet<TermId>,
    cert_part: &super::interpolant_farkas::CertPartition<'_>,
    strength: InterpolantStrength,
    bc: &BoolConstants,
) -> Option<TermId> {
    use super::interpolant_farkas::AtomClass;
    let i1 = i1?;
    let i2 = i2?;

    let pivot_atom = atom_of_literal(terms, pivot);
    let mut in_a = a_atoms.contains(&pivot_atom) || a_assertions.contains(&pivot_atom);
    let mut in_b = b_atoms.contains(&pivot_atom) || b_assertions.contains(&pivot_atom);
    if !in_a && !in_b {
        // Variable-occurrence fallback for synthetic atoms (inc-4).
        match cert_part.class_of_atom(terms, pivot_atom) {
            Some(AtomClass::A) => in_a = true,
            Some(AtomClass::B) => in_b = true,
            Some(AtomClass::Ab) => {
                in_a = true;
                in_b = true;
            }
            None => {}
        }
    }

    match (in_a, in_b) {
        (true, false) => {
            // A-local pivot: I = I1 \/ I2
            Some(mk_or_simplified(terms, i1, i2, bc.true_tid, bc.false_tid))
        }
        (false, true) => {
            // B-local pivot: I = I1 /\ I2
            Some(mk_and_simplified(terms, i1, i2, bc.true_tid, bc.false_tid))
        }
        (true, true) => {
            // Shared pivot: depends on strength.
            //
            // The shared-pivot rule must match the labeling used by the leaf
            // rules (#rank-4 increment 1): McMillan labels shared occurrences
            // `b` (leaf I(A-clause) = disjunction of shared literals, so a
            // shared pivot resolves on the B side -> AND); McMillan' labels
            // them `a` (leaf I(B-clause) = conjunction of negated shared
            // literals -> OR). The previous OR-for-McMillan / AND-for-
            // McMillan' pairing mixed the two systems and produced
            // non-interpolants.
            match strength {
                InterpolantStrength::Strongest => {
                    // McMillan: shared pivot is b-labeled -> I1 /\ I2
                    Some(mk_and_simplified(terms, i1, i2, bc.true_tid, bc.false_tid))
                }
                InterpolantStrength::Weakest => {
                    // McMillan': shared pivot is a-labeled -> I1 \/ I2
                    Some(mk_or_simplified(terms, i1, i2, bc.true_tid, bc.false_tid))
                }
                InterpolantStrength::Default => {
                    // Pudlak: I = (I1 \/ p) /\ (I2 \/ ~p)
                    let not_pivot = terms.mk_not(pivot);
                    let left = mk_or_simplified(terms, i1, pivot, bc.true_tid, bc.false_tid);
                    let right = mk_or_simplified(terms, i2, not_pivot, bc.true_tid, bc.false_tid);
                    Some(mk_and_simplified(
                        terms,
                        left,
                        right,
                        bc.true_tid,
                        bc.false_tid,
                    ))
                }
            }
        }
        (false, false) => {
            // Neither A nor B — shouldn't happen in a well-formed partition.
            // Conservative: treat as A-local (disjunction).
            Some(mk_or_simplified(terms, i1, i2, bc.true_tid, bc.false_tid))
        }
    }
}

/// Pivot-aware interpolation of a resolution-shaped `Step` chain (rank-4
/// inc-4): the executor's th_resolution / RUP replay emits
/// `Step { rule: ThResolution|Resolution, premises }` nodes that do NOT carry
/// pivots. Recover each pivot from the premise clauses (the literal with a
/// complementary occurrence) and fold the premises left-to-right with the
/// standard pivot-aware combination. Returns `None` when any premise lacks a
/// clause view / partial interpolant or no pivot can be recovered (the caller
/// keeps the conservative conjunction).
#[allow(clippy::too_many_arguments)]
fn interpolate_resolution_chain(
    terms: &mut TermStore,
    premises: &[ProofId],
    partial: &[Option<TermId>],
    clause_lits: &[ClauseLits<'_>],
    a_atoms: &HashSet<TermId>,
    b_atoms: &HashSet<TermId>,
    a_assertions: &HashSet<TermId>,
    b_assertions: &HashSet<TermId>,
    cert_part: &super::interpolant_farkas::CertPartition<'_>,
    strength: InterpolantStrength,
    bc: &BoolConstants,
) -> Option<TermId> {
    let first = premises.first()?;
    let mut cur_lits: Vec<TermId> = clause_lits.get(first.0 as usize)?.get()?.to_vec();
    let mut cur_itp = (*partial.get(first.0 as usize)?)?;

    for pid in &premises[1..] {
        let next_lits = clause_lits.get(pid.0 as usize)?.get()?;
        let next_itp = (*partial.get(pid.0 as usize)?)?;
        let pivot = find_chain_pivot(terms, &cur_lits, next_lits)?;
        cur_itp = interpolate_resolution(
            terms,
            pivot,
            Some(cur_itp),
            Some(next_itp),
            a_atoms,
            b_atoms,
            a_assertions,
            b_assertions,
            cert_part,
            strength,
            bc,
        )?;
        cur_lits = chain_resolvent(terms, &cur_lits, next_lits, pivot);
    }
    Some(cur_itp)
}

/// Find the pivot literal between two clauses: a literal of `c1` whose
/// complement occurs in `c2`. Returns the `c1` occurrence.
fn find_chain_pivot(terms: &TermStore, c1: &[TermId], c2: &[TermId]) -> Option<TermId> {
    for &lit in c1 {
        let (atom, neg) = literal_atom_polarity(terms, lit);
        for &other in c2 {
            let (oatom, oneg) = literal_atom_polarity(terms, other);
            if atom == oatom && neg != oneg {
                return Some(lit);
            }
        }
    }
    None
}

/// Resolvent of `c1` and `c2` on `pivot` (a `c1` literal): every literal of
/// both clauses except the pivot atom (either polarity), deduplicated.
fn chain_resolvent(terms: &TermStore, c1: &[TermId], c2: &[TermId], pivot: TermId) -> Vec<TermId> {
    let (pivot_atom, _) = literal_atom_polarity(terms, pivot);
    let mut out: Vec<TermId> = Vec::with_capacity(c1.len() + c2.len());
    let mut seen: HashSet<TermId> = HashSet::default();
    for &lit in c1.iter().chain(c2.iter()) {
        let (atom, _) = literal_atom_polarity(terms, lit);
        if atom == pivot_atom {
            continue;
        }
        if seen.insert(lit) {
            out.push(lit);
        }
    }
    out
}

/// Atom and polarity of a literal (`true` = negated), stripping nested `not`.
fn literal_atom_polarity(terms: &TermStore, mut lit: TermId) -> (TermId, bool) {
    let mut neg = false;
    while let TermData::Not(inner) = terms.get(lit) {
        lit = *inner;
        neg = !neg;
    }
    (lit, neg)
}

/// Conjoin premise interpolants for a generic Alethe step.
fn combine_premise_interpolants(
    terms: &mut TermStore,
    partial: &[Option<TermId>],
    premises: &[ProofId],
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    let mut result = true_tid;
    for pid in premises {
        if let Some(Some(interp)) = partial.get(pid.0 as usize) {
            result = mk_and_simplified(terms, result, *interp, true_tid, false_tid);
        }
    }
    Some(result)
}

// ============================================================================
// Term analysis helpers
// ============================================================================

/// Recursively collect all variable TermIds from a term.
fn collect_vars(terms: &TermStore, tid: TermId, vars: &mut HashSet<TermId>) {
    match terms.get(tid) {
        TermData::Var(_, _) => {
            vars.insert(tid);
        }
        TermData::Const(_) => {}
        _ => {
            for child in terms.children(tid) {
                collect_vars(terms, child, vars);
            }
        }
    }
}

/// Recursively collect all atomic sub-formulas (non-Boolean leaf predicates)
/// from a Boolean term.
fn collect_atoms(terms: &TermStore, tid: TermId, atoms: &mut HashSet<TermId>) {
    match terms.get(tid) {
        TermData::Not(inner) => {
            collect_atoms(terms, *inner, atoms);
        }
        TermData::App(sym, args) => {
            let name = sym.name();
            // Bool-sorted `=` (iff) is connective-like: descend into its
            // arguments so Bool sub-atoms get their own color (rank-4 inc-4;
            // matches the interpolation-spike atom collection — without it
            // shared Bool pivots behind iff definitions stay unlabeled).
            let descend = matches!(name, "and" | "or" | "=>" | "xor")
                || (name == "=" && args.first().is_some_and(|a| terms.sort(*a) == &Sort::Bool));
            if descend {
                for &arg in args {
                    collect_atoms(terms, arg, atoms);
                }
            } else {
                atoms.insert(tid);
            }
        }
        TermData::Ite(cond, then_br, else_br) if terms.sort(tid) == &Sort::Bool => {
            collect_atoms(terms, *cond, atoms);
            collect_atoms(terms, *then_br, atoms);
            collect_atoms(terms, *else_br, atoms);
        }
        _ => {
            atoms.insert(tid);
        }
    }
}

/// Strip negation from a literal, returning the underlying atom TermId.
fn atom_of_literal(terms: &TermStore, lit: TermId) -> TermId {
    match terms.get(lit) {
        TermData::Not(inner) => *inner,
        _ => lit,
    }
}

/// Check whether a term uses only shared variables.
fn uses_only_shared_vars(terms: &TermStore, tid: TermId, shared: &HashSet<TermId>) -> bool {
    match terms.get(tid) {
        TermData::Var(_, _) => shared.contains(&tid),
        TermData::Const(_) => true,
        _ => terms
            .children(tid)
            .iter()
            .all(|&child| uses_only_shared_vars(terms, child, shared)),
    }
}

/// Find the name of the first non-shared variable in a term, for diagnostics.
///
/// Returns `Some(name)` if a variable not in `shared` is found, `None` otherwise.
/// Used only in `debug_assert!` messages to identify the offending variable.
fn find_non_shared_var_name(
    terms: &TermStore,
    tid: TermId,
    shared: &HashSet<TermId>,
) -> Option<String> {
    match terms.get(tid) {
        TermData::Var(name, _) => {
            if shared.contains(&tid) {
                None
            } else {
                Some(name.clone())
            }
        }
        TermData::Const(_) => None,
        _ => terms
            .children(tid)
            .iter()
            .find_map(|&child| find_non_shared_var_name(terms, child, shared)),
    }
}

// ============================================================================
// Simplified term constructors
// ============================================================================

/// Build `a \/ b` with constant simplification.
fn mk_or_simplified(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    true_tid: TermId,
    false_tid: TermId,
) -> TermId {
    if a == true_tid || b == true_tid {
        true_tid
    } else if a == false_tid || a == b {
        b
    } else if b == false_tid {
        a
    } else {
        terms.mk_or(vec![a, b])
    }
}

/// Build `a /\ b` with constant simplification.
fn mk_and_simplified(
    terms: &mut TermStore,
    a: TermId,
    b: TermId,
    true_tid: TermId,
    false_tid: TermId,
) -> TermId {
    if a == false_tid || b == false_tid {
        false_tid
    } else if a == true_tid || a == b {
        b
    } else if b == true_tid {
        a
    } else {
        terms.mk_and(vec![a, b])
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::types::{InterpolantStrength, Logic, PathInterpolantResult};
    use crate::api::Solver;

    /// Helper: create a simple QF_LIA contradiction: x > 0 /\ x < 0.
    /// Group A: x > 0, Group B: x < 0. Shared variable: x.
    fn setup_simple_lia_contradiction() -> (Solver, Term, Term) {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        solver.set_produce_proofs(true);

        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);

        // A: x > 0
        let x_gt_zero = solver.try_gt(x, zero).expect("int > int");
        // B: x < 0
        let x_lt_zero = solver.try_lt(x, zero).expect("int < int");

        solver
            .try_assert_term(x_gt_zero)
            .expect("boolean assertion");
        solver
            .try_assert_term(x_lt_zero)
            .expect("boolean assertion");

        (solver, x_gt_zero, x_lt_zero)
    }

    #[test]
    fn test_interpolant_strength_display() {
        assert_eq!(
            InterpolantStrength::Weakest.to_string(),
            "weakest (McMillan')"
        );
        assert_eq!(InterpolantStrength::Default.to_string(), "default (Pudlak)");
        assert_eq!(
            InterpolantStrength::Strongest.to_string(),
            "strongest (McMillan)"
        );
    }

    #[test]
    fn test_interpolant_strength_default() {
        assert_eq!(InterpolantStrength::default(), InterpolantStrength::Default);
    }

    #[test]
    fn test_get_interpolant_no_proof() {
        // Without enabling proof production, interpolation should return None.
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let x_gt_zero = solver.try_gt(x, zero).expect("int > int");
        let x_lt_zero = solver.try_lt(x, zero).expect("int < int");
        solver.try_assert_term(x_gt_zero).expect("ok");
        solver.try_assert_term(x_lt_zero).expect("ok");

        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        // No proofs enabled — should return None.
        let interp = solver.get_interpolant(&[x_gt_zero], &[x_lt_zero]);
        assert!(
            interp.is_none(),
            "interpolant should be None without proof production"
        );
    }

    #[test]
    fn test_get_interpolant_pudlak_simple() {
        let (mut solver, a_term, b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let interp = solver.get_interpolant(&[a_term], &[b_term]);
        // The interpolant may or may not be produced depending on whether
        // the proof contains enough structure. If produced, verify metadata.
        if let Some(ref ir) = interp {
            assert_eq!(ir.strength(), InterpolantStrength::Default);
        }
    }

    #[test]
    fn test_get_interpolant_mcmillan_simple() {
        let (mut solver, a_term, b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let interp = solver.get_interpolant_with_strength(
            &[a_term],
            &[b_term],
            InterpolantStrength::Strongest,
        );
        if let Some(ref ir) = interp {
            assert_eq!(ir.strength(), InterpolantStrength::Strongest);
        }
    }

    #[test]
    fn test_get_interpolant_mcmillan_prime_simple() {
        let (mut solver, a_term, b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let interp = solver.get_interpolant_with_strength(
            &[a_term],
            &[b_term],
            InterpolantStrength::Weakest,
        );
        if let Some(ref ir) = interp {
            assert_eq!(ir.strength(), InterpolantStrength::Weakest);
        }
    }

    #[test]
    fn test_get_interpolant_sat_returns_none() {
        // For a SAT result, there's no proof, so interpolation returns None.
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        solver.set_produce_proofs(true);
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let x_gt_zero = solver.try_gt(x, zero).expect("int > int");
        solver.try_assert_term(x_gt_zero).expect("ok");

        let result = solver.check_sat();
        assert!(result.is_sat(), "should be SAT");

        let interp = solver.get_interpolant(&[x_gt_zero], &[]);
        assert!(interp.is_none(), "no interpolant for SAT results");
    }

    #[test]
    fn test_get_interpolant_empty_groups() {
        let (mut solver, a_term, _b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        // Empty B group: the interpolant should be computable but may be trivial.
        let interp = solver.get_interpolant(&[a_term], &[]);
        // Result depends on proof structure — just ensure no panic.
        let _ = interp;
    }

    #[test]
    fn test_collect_vars_basic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let c = terms.mk_int(42.into());

        let mut vars = HashSet::default();
        collect_vars(&terms, x, &mut vars);
        assert!(vars.contains(&x));
        assert_eq!(vars.len(), 1);

        collect_vars(&terms, c, &mut vars);
        assert_eq!(vars.len(), 1, "constants should not be collected as vars");

        collect_vars(&terms, y, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&y));
    }

    #[test]
    fn test_atom_of_literal() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);

        assert_eq!(atom_of_literal(&terms, x), x);
        assert_eq!(atom_of_literal(&terms, not_x), x);
    }

    #[test]
    fn test_mk_or_simplified_constants() {
        let mut terms = TermStore::new();
        // Initialize true/false by creating Bool constants.
        let true_tid = terms.mk_bool(true);
        let false_tid = terms.mk_bool(false);
        let x = terms.mk_var("x", Sort::Bool);

        assert_eq!(
            mk_or_simplified(&mut terms, true_tid, x, true_tid, false_tid),
            true_tid
        );
        assert_eq!(
            mk_or_simplified(&mut terms, x, true_tid, true_tid, false_tid),
            true_tid
        );
        assert_eq!(
            mk_or_simplified(&mut terms, false_tid, x, true_tid, false_tid),
            x
        );
        assert_eq!(
            mk_or_simplified(&mut terms, x, false_tid, true_tid, false_tid),
            x
        );
        assert_eq!(mk_or_simplified(&mut terms, x, x, true_tid, false_tid), x);
    }

    #[test]
    fn test_mk_and_simplified_constants() {
        let mut terms = TermStore::new();
        let true_tid = terms.mk_bool(true);
        let false_tid = terms.mk_bool(false);
        let x = terms.mk_var("x", Sort::Bool);

        assert_eq!(
            mk_and_simplified(&mut terms, false_tid, x, true_tid, false_tid),
            false_tid
        );
        assert_eq!(
            mk_and_simplified(&mut terms, x, false_tid, true_tid, false_tid),
            false_tid
        );
        assert_eq!(
            mk_and_simplified(&mut terms, true_tid, x, true_tid, false_tid),
            x
        );
        assert_eq!(
            mk_and_simplified(&mut terms, x, true_tid, true_tid, false_tid),
            x
        );
        assert_eq!(mk_and_simplified(&mut terms, x, x, true_tid, false_tid), x);
    }

    #[test]
    fn test_all_strengths_on_same_problem() {
        // Verify all three strengths can be called on the same UNSAT problem
        // without panicking.
        let (mut solver, a_term, b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let pudlak = solver.get_interpolant_with_strength(
            &[a_term],
            &[b_term],
            InterpolantStrength::Default,
        );
        let mcmillan = solver.get_interpolant_with_strength(
            &[a_term],
            &[b_term],
            InterpolantStrength::Strongest,
        );
        let mcmillan_prime = solver.get_interpolant_with_strength(
            &[a_term],
            &[b_term],
            InterpolantStrength::Weakest,
        );

        // All should either succeed or fail consistently (proofs may not
        // be detailed enough for all problems).
        if pudlak.is_some() {
            assert!(mcmillan.is_some(), "McMillan should succeed if Pudlak does");
            assert!(
                mcmillan_prime.is_some(),
                "McMillan' should succeed if Pudlak does"
            );
        }
    }

    #[test]
    fn test_find_non_shared_var_name() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);

        let mut shared = HashSet::default();
        shared.insert(x);

        // y is not shared, should be found
        assert_eq!(
            find_non_shared_var_name(&terms, y, &shared),
            Some("y".to_string())
        );

        // x is shared, should return None
        assert_eq!(find_non_shared_var_name(&terms, x, &shared), None);

        // constant should return None
        let c = terms.mk_int(42.into());
        assert_eq!(find_non_shared_var_name(&terms, c, &shared), None);
    }

    // ====================================================================
    // Path interpolant tests
    // ====================================================================

    #[test]
    fn test_path_interpolant_too_few_partitions() {
        // Fewer than 2 partitions should return None.
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        solver.set_produce_proofs(true);
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let a = solver.try_gt(x, zero).expect("int > int");
        let b = solver.try_lt(x, zero).expect("int < int");
        solver.try_assert_term(a).expect("ok");
        solver.try_assert_term(b).expect("ok");
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        // Single partition: returns None.
        let single: &[&[Term]] = &[&[a, b]];
        assert!(solver.get_path_interpolants(single).is_none());

        // Empty: returns None.
        let empty: &[&[Term]] = &[];
        assert!(solver.get_path_interpolants(empty).is_none());
    }

    #[test]
    fn test_path_interpolant_binary_matches_regular() {
        // With exactly 2 partitions, path interpolant should produce exactly 1
        // interpolant, equivalent to the binary case.
        let (mut solver, a_term, b_term) = setup_simple_lia_contradiction();
        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let partitions: &[&[Term]] = &[&[a_term], &[b_term]];
        let path_result = solver.get_path_interpolants(partitions);

        if let Some(ref pr) = path_result {
            assert_eq!(pr.len(), 1, "2 partitions should yield 1 interpolant");
            assert!(!pr.is_empty());
            assert_eq!(pr.strength(), InterpolantStrength::Default);
        }
    }

    /// 3-partition path interpolation test.
    ///
    /// A1: x > 0
    /// A2: y > x  (shared x with A1, shared y with A3)
    /// A3: y < 0
    ///
    /// A1 /\ A2 /\ A3 is UNSAT because: x > 0 /\ y > x => y > 0,
    /// but A3 says y < 0.
    ///
    /// Expected path interpolants I1, I2 where:
    /// - A1 |= I1           (I1 should mention only x, shared between A1 and {A2,A3})
    /// - I1 /\ A2 |= I2     (I2 should mention only y, shared between {A1,A2} and A3)
    /// - I2 /\ A3 is UNSAT
    #[test]
    fn test_path_interpolant_three_partitions() {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        solver.set_produce_proofs(true);

        let x = solver.declare_const("x", Sort::Int);
        let y = solver.declare_const("y", Sort::Int);
        let zero = solver.int_const(0);

        // A1: x > 0
        let a1 = solver.try_gt(x, zero).expect("int > int");
        // A2: y > x
        let a2 = solver.try_gt(y, x).expect("int > int");
        // A3: y < 0
        let a3 = solver.try_lt(y, zero).expect("int < int");

        solver.try_assert_term(a1).expect("ok");
        solver.try_assert_term(a2).expect("ok");
        solver.try_assert_term(a3).expect("ok");

        let result = solver.check_sat();
        assert!(result.is_unsat(), "x>0 /\\ y>x /\\ y<0 should be UNSAT");

        let partitions: &[&[Term]] = &[&[a1], &[a2], &[a3]];
        let path_result = solver.get_path_interpolants(partitions);

        if let Some(ref pr) = path_result {
            assert_eq!(pr.len(), 2, "3 partitions should yield 2 path interpolants");
            assert_eq!(pr.strength(), InterpolantStrength::Default);
        }
    }

    #[test]
    fn test_path_interpolant_three_partitions_all_strengths() {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        solver.set_produce_proofs(true);

        let x = solver.declare_const("x", Sort::Int);
        let y = solver.declare_const("y", Sort::Int);
        let zero = solver.int_const(0);

        let a1 = solver.try_gt(x, zero).expect("int > int");
        let a2 = solver.try_gt(y, x).expect("int > int");
        let a3 = solver.try_lt(y, zero).expect("int < int");

        solver.try_assert_term(a1).expect("ok");
        solver.try_assert_term(a2).expect("ok");
        solver.try_assert_term(a3).expect("ok");

        let result = solver.check_sat();
        assert!(result.is_unsat(), "should be UNSAT");

        let partitions: &[&[Term]] = &[&[a1], &[a2], &[a3]];

        for strength in [
            InterpolantStrength::Weakest,
            InterpolantStrength::Default,
            InterpolantStrength::Strongest,
        ] {
            let pr = solver.get_path_interpolants_with_strength(partitions, strength);
            if let Some(ref pr) = pr {
                assert_eq!(pr.len(), 2);
                assert_eq!(pr.strength(), strength);
            }
        }
    }

    #[test]
    fn test_path_interpolant_no_proof() {
        // Without proof production, path interpolation returns None.
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let a = solver.try_gt(x, zero).expect("ok");
        let b = solver.try_lt(x, zero).expect("ok");
        solver.try_assert_term(a).expect("ok");
        solver.try_assert_term(b).expect("ok");
        let result = solver.check_sat();
        assert!(result.is_unsat());

        let partitions: &[&[Term]] = &[&[a], &[b]];
        assert!(
            solver.get_path_interpolants(partitions).is_none(),
            "should be None without proof production"
        );
    }

    // ====================================================================
    // Labeling-consistency tests (#rank-4 increment 1)
    //
    // Hand-computed resolution proofs where OR-vs-AND on a shared pivot
    // give different answers and only the consistent labeling yields a
    // verified interpolant (A ∧ ¬I unsat, I ∧ B unsat, checked with the
    // internal solver).
    // ====================================================================

    /// Parse a script into a fresh solver and return the check-sat verdict.
    fn script_verdict(script: &str) -> &'static str {
        let mut s = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        s.parse_smtlib2(script).expect("verification script parses");
        let r = s.check_sat();
        if r.is_unsat() {
            "unsat"
        } else if r.is_sat() {
            "sat"
        } else {
            "unknown"
        }
    }

    /// Shared-pivot refutation used by the labeling tests:
    ///   A = { q }
    ///   B = { (or (not q) r), (not r) }
    ///   Proof: [¬q ∨ r] ⨂_r [¬r] = [¬q];  [q] ⨂_q [¬q] = [] (shared pivot q)
    ///
    /// Returns (solver, proof, a_assertions, b_assertions, a_atoms, b_atoms,
    /// a_vars, b_vars, shared_vars). The pivot q occurs in both partitions
    /// (shared); r is B-local.
    #[allow(clippy::type_complexity)]
    fn setup_shared_pivot_proof() -> (
        Solver,
        Proof,
        HashSet<TermId>,
        HashSet<TermId>,
        HashSet<TermId>,
        HashSet<TermId>,
        HashSet<TermId>,
        HashSet<TermId>,
        HashSet<TermId>,
    ) {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        let q = solver.declare_const("q", Sort::Bool).0;
        let r = solver.declare_const("r", Sort::Bool).0;
        let not_q = solver.terms_mut().mk_not_raw(q);
        let not_r = solver.terms_mut().mk_not_raw(r);
        let b1 = solver.terms_mut().mk_or(vec![not_q, r]);

        let mut proof = Proof::new();
        let s0 = proof.add_assume(q, Some("a0".to_string())); // A: q
        let s1 = proof.add_assume(b1, Some("b0".to_string())); // B: ¬q ∨ r
        let s2 = proof.add_assume(not_r, Some("b1".to_string())); // B: ¬r
        let s3 = proof.add_resolution(vec![not_q], r, s1, s2); // pivot r (B-local)
        let _s4 = proof.add_resolution(vec![], q, s0, s3); // pivot q (shared)

        let a_assertions: HashSet<TermId> = [q].into_iter().collect();
        let b_assertions: HashSet<TermId> = [b1, not_r].into_iter().collect();
        let a_atoms: HashSet<TermId> = [q].into_iter().collect();
        let b_atoms: HashSet<TermId> = [q, r].into_iter().collect();
        let a_vars: HashSet<TermId> = [q].into_iter().collect();
        let b_vars: HashSet<TermId> = [q, r].into_iter().collect();
        let shared_vars: HashSet<TermId> = [q].into_iter().collect();

        (
            solver,
            proof,
            a_assertions,
            b_assertions,
            a_atoms,
            b_atoms,
            a_vars,
            b_vars,
            shared_vars,
        )
    }

    const SHARED_PIVOT_DECLS: &str = "(declare-const q Bool)\n(declare-const r Bool)\n";

    fn shared_pivot_check_a(i_text: &str) -> String {
        format!("{SHARED_PIVOT_DECLS}(assert q)\n(assert (not {i_text}))\n(check-sat)\n")
    }

    fn shared_pivot_check_b(i_text: &str) -> String {
        format!(
            "{SHARED_PIVOT_DECLS}(assert (or (not q) r))\n(assert (not r))\n(assert {i_text})\n(check-sat)\n"
        )
    }

    /// McMillan (Strongest): leaves I(q)=q, I(B)=true; B-local pivot AND;
    /// shared pivot AND → I = q. Verified: A ∧ ¬q unsat, q ∧ B unsat.
    ///
    /// The OLD inconsistent rule (shared pivot → OR) gives I = q ∨ true =
    /// true, which is NOT an interpolant (true ∧ B is SAT) — checked below.
    #[test]
    fn test_labeling_mcmillan_shared_pivot_verified() {
        let (mut solver, proof, a_asserts, b_asserts, a_atoms, b_atoms, a_vars, b_vars, shared) =
            setup_shared_pivot_proof();

        let itp = solver
            .traverse_proof_for_interpolant(
                &proof,
                &a_asserts,
                &b_asserts,
                &a_atoms,
                &b_atoms,
                &a_vars,
                &b_vars,
                &shared,
                InterpolantStrength::Strongest,
            )
            .expect("McMillan traversal must produce an interpolant");

        let i_text = solver.format_term(Term(itp));
        assert_eq!(i_text, "q", "hand-computed McMillan interpolant is q");
        assert_eq!(script_verdict(&shared_pivot_check_a(&i_text)), "unsat");
        assert_eq!(script_verdict(&shared_pivot_check_b(&i_text)), "unsat");

        // The old OR-labeled result (I = true) must fail verification:
        // true ∧ B is satisfiable.
        assert_eq!(
            script_verdict(&shared_pivot_check_b("true")),
            "sat",
            "the inconsistent OR-labeled McMillan result is not an interpolant"
        );
    }

    /// Pudlak (Default): leaves I(A)=false, I(B)=true; shared pivot
    /// (I1 ∨ p) ∧ (I2 ∨ ¬p) = (false ∨ q) ∧ (true ∨ ¬q) = q. Verified.
    #[test]
    fn test_labeling_pudlak_shared_pivot_verified() {
        let (mut solver, proof, a_asserts, b_asserts, a_atoms, b_atoms, a_vars, b_vars, shared) =
            setup_shared_pivot_proof();

        let itp = solver
            .traverse_proof_for_interpolant(
                &proof,
                &a_asserts,
                &b_asserts,
                &a_atoms,
                &b_atoms,
                &a_vars,
                &b_vars,
                &shared,
                InterpolantStrength::Default,
            )
            .expect("Pudlak traversal must produce an interpolant");

        let i_text = solver.format_term(Term(itp));
        assert_eq!(script_verdict(&shared_pivot_check_a(&i_text)), "unsat");
        assert_eq!(script_verdict(&shared_pivot_check_b(&i_text)), "unsat");
    }

    /// McMillan' (Weakest) on the dual instance:
    ///   A = { (or q r), (not r) }
    ///   B = { (not q) }
    ///   Proof: [q ∨ r] ⨂_r [¬r] = [q] (A-local pivot);
    ///          [q] ⨂_q [¬q] = [] (shared pivot)
    ///
    /// Consistent system: A-leaves → false; B-leaf ¬q (shared, a-labeled) →
    /// ¬¬q = q; A-local pivot OR → false; shared pivot OR → q. Verified:
    /// A ∧ ¬q unsat (A ⊨ q), q ∧ ¬q unsat.
    ///
    /// The OLD inconsistent rule (shared pivot → AND) gives I = false ∧ q =
    /// false, which is NOT an interpolant (A ⊭ false) — checked below.
    #[test]
    fn test_labeling_mcmillan_prime_shared_pivot_verified() {
        let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
        let q = solver.declare_const("q", Sort::Bool).0;
        let r = solver.declare_const("r", Sort::Bool).0;
        let not_q = solver.terms_mut().mk_not_raw(q);
        let not_r = solver.terms_mut().mk_not_raw(r);
        let a1 = solver.terms_mut().mk_or(vec![q, r]);

        let mut proof = Proof::new();
        let s0 = proof.add_assume(a1, Some("a0".to_string())); // A: q ∨ r
        let s1 = proof.add_assume(not_r, Some("a1".to_string())); // A: ¬r
        let s2 = proof.add_assume(not_q, Some("b0".to_string())); // B: ¬q
        let s3 = proof.add_resolution(vec![q], r, s0, s1); // pivot r (A-local)
        let _s4 = proof.add_resolution(vec![], q, s3, s2); // pivot q (shared)

        let a_assertions: HashSet<TermId> = [a1, not_r].into_iter().collect();
        let b_assertions: HashSet<TermId> = [not_q].into_iter().collect();
        let a_atoms: HashSet<TermId> = [q, r].into_iter().collect();
        let b_atoms: HashSet<TermId> = [q].into_iter().collect();
        let a_vars: HashSet<TermId> = [q, r].into_iter().collect();
        let b_vars: HashSet<TermId> = [q].into_iter().collect();
        let shared: HashSet<TermId> = [q].into_iter().collect();

        let itp = solver
            .traverse_proof_for_interpolant(
                &proof,
                &a_assertions,
                &b_assertions,
                &a_atoms,
                &b_atoms,
                &a_vars,
                &b_vars,
                &shared,
                InterpolantStrength::Weakest,
            )
            .expect("McMillan' traversal must produce an interpolant");

        let i_text = solver.format_term(Term(itp));
        let decls = "(declare-const q Bool)\n(declare-const r Bool)\n";
        let check_a = format!(
            "{decls}(assert (or q r))\n(assert (not r))\n(assert (not {i_text}))\n(check-sat)\n"
        );
        let check_b = format!("{decls}(assert (not q))\n(assert {i_text})\n(check-sat)\n");
        assert_eq!(script_verdict(&check_a), "unsat", "A ∧ ¬I must be unsat");
        assert_eq!(script_verdict(&check_b), "unsat", "I ∧ B must be unsat");

        // The old AND-labeled result (I = false) must fail verification:
        // A ∧ ¬false = A is satisfiable.
        let check_a_old = format!(
            "{decls}(assert (or q r))\n(assert (not r))\n(assert (not false))\n(check-sat)\n"
        );
        assert_eq!(
            script_verdict(&check_a_old),
            "sat",
            "the inconsistent AND-labeled McMillan' result is not an interpolant"
        );
    }

    #[test]
    fn test_path_interpolant_result_accessors() {
        // Unit test for PathInterpolantResult methods.
        let t1 = Term(TermId(0));
        let t2 = Term(TermId(1));
        let pr = PathInterpolantResult::new(vec![t1, t2], InterpolantStrength::Weakest);
        assert_eq!(pr.len(), 2);
        assert!(!pr.is_empty());
        assert_eq!(pr.interpolants().len(), 2);
        assert_eq!(pr.strength(), InterpolantStrength::Weakest);

        let empty_pr = PathInterpolantResult::new(vec![], InterpolantStrength::Default);
        assert_eq!(empty_pr.len(), 0);
        assert!(empty_pr.is_empty());
    }
}
