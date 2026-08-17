// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData as Td;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};
use ay_sat::{Literal, Variable};

use crate::executor::Executor;

/// Upper bound on the problem-assertion count that
/// [`Executor::rebuild_relaxation_forced_arith_farkas`] will attempt to
/// reconstruct. The MaxSMT/optimization feasibility probes are small; a larger
/// assertion set is left for the fail-closed trust fallback rather than seeding
/// a costly bounded DPLL(T) scan.
const MAX_RELAXATION_FARKAS_ROOTS: usize = 4096;

/// A literal is a Boolean-var atom or a binary </<=/>/>=/= atom, in either
/// polarity (one optional `not`). Returns `(atom, value)`.
fn literal_atom(terms: &TermStore, lit: TermId) -> Option<(TermId, bool)> {
    let (atom, value) = match terms.get(lit) {
        Td::Not(inner) => (*inner, false),
        _ => (lit, true),
    };
    let usable = match terms.get(atom) {
        Td::Var(..) => matches!(terms.sort(atom), Sort::Bool),
        Td::App(Symbol::Named(name), args) => {
            args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
        }
        _ => false,
    };
    usable.then_some((atom, value))
}

impl Executor {
    /// Rebuild a genuine, strict-checkable Farkas refutation for a
    /// relaxation-encoded LIA/LRA UNSAT whose proof otherwise collapsed to a
    /// whole-problem `trust` step.
    ///
    /// The checked isolated feasibility probe used by MaxSMT/optimization
    /// re-solves an INJECTED assertion vector (raw `TermId`s, no parsed-command
    /// provenance). When the relaxation cardinality pins every soft selector,
    /// the forced theory literals (`x > 5`, `x < 3`, …) are jointly LIA/LRA
    /// infeasible, but that UNSAT is detected without a materialized SAT trace,
    /// so it collapses to a single whole-problem `trust` leaf — which fails
    /// strict checking, and (lacking source provenance) none of the authored
    /// replacement cascades can rebuild it. The probe then degrades a correct
    /// `unsat` to `unknown`, blocking the whole MaxSMT/optimization cluster.
    ///
    /// This pass reconstructs the honest proof the trace-driven pipeline would
    /// have produced. It rebuilds the clause database DIRECTLY from the problem
    /// assertions — every one of which is an authorized `assume` — and hands it
    /// to the bounded DPLL(T) closer. That closer unit-propagates through the
    /// relaxation/cardinality clauses (bridging the relaxation gap by GENUINE
    /// resolution — the forced theory literals are derived, never assumed),
    /// certifies the forced arithmetic conflict with a fresh `LraSolver` Farkas
    /// certificate, and folds everything into ordinary `Resolution` steps over
    /// an `la_generic`-printable `LraFarkas` lemma.
    ///
    /// SOUNDNESS / fail-closed at every gate:
    /// * runs ONLY when the current proof is not already strict-complete, so a
    ///   valid proof (e.g. a bounded `BvLiaTautology` internal certificate) is
    ///   preserved byte-identically;
    /// * declines unless EVERY problem assertion is a propagatable clause (a
    ///   unit literal or a flat `(or …)` of Bool/arith literals) — the exact CNF
    ///   shape the relaxation encoding produces — so it never mis-handles a
    ///   nested formula;
    /// * the assumptions are the exact strict-proof scope, so every rebuilt
    ///   `assume` is authorized;
    /// * the candidate REPLACES the trust proof only after it independently
    ///   re-checks strict-complete (the strict checker re-derives every Farkas
    ///   combination); any gap leaves the original proof untouched.
    pub(crate) fn rebuild_relaxation_forced_arith_farkas(&mut self, proof: &mut Proof) {
        // (0) Only repair a proof that still rides on a `trust`/`hole` fallback
        // on its path to the empty clause. This is a cheap backwards walk — NOT
        // a strict-check invocation — so a clean, already-certified UNSAT (the
        // common case) is left untouched with zero added strict-check accounting
        // (the #strict-verdict-memo publication budget is preserved).
        if ay_proof::terminal_trust_report(proof).is_trust_free() {
            return;
        }

        // (1) Authorized roots = the exact scope strict checking validates
        // assumptions against, so every rebuilt `assume` stays in problem scope.
        let roots = self.complete_problem_assertions_for_strict_proof();
        // Bound the reconstruction: the relaxation feasibility probes are small,
        // and a very large assertion set would make the seeded DPLL(T) scan
        // costly for no benefit. Empty or oversized -> leave the proof untouched.
        if roots.is_empty() || roots.len() > MAX_RELAXATION_FARKAS_ROOTS {
            return;
        }

        // (2) Seed a propagatable clause database from the CNF relaxation roots.
        // Declines (fail-closed) on any non-CNF assertion.
        let Some((var_to_term, clause_versions, mut candidate)) =
            self.seed_relaxation_clause_database(&roots)
        else {
            return;
        };

        // (3) Hand the seeded clause database to the bounded DPLL(T) closer.
        let empty_id = {
            let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
            manager.close_empty_over_seeded_clauses(&clause_versions, &mut candidate)
        };
        let Some(empty_id) = empty_id else {
            return;
        };

        // (4) Prune to the empty-clause cone and accept ONLY on a strict,
        // complete re-check. The strict checker is the sole arbiter; a bad
        // certificate is rejected here and the original trust proof stands.
        if !crate::executor::proof_resolution::prune_to_empty_clause_derivation_at(
            &mut candidate,
            empty_id.0 as usize,
        ) {
            return;
        }
        if self
            .check_proof_strict_with_datatypes(&candidate)
            .is_ok_and(|quality| quality.is_complete())
        {
            *proof = candidate;
        }
    }

    /// Seed a propagatable clause database plus a candidate proof directly from
    /// the problem assertions, for [`Self::rebuild_relaxation_forced_arith_farkas`].
    ///
    /// Returns `None` (declines fail-closed) unless EVERY root is a unit literal
    /// or a flat `(or …)` of Boolean-var / binary-comparison literals — the exact
    /// CNF relaxation shape — and at least one arithmetic atom participates. On
    /// success returns the SAT `var_to_term` map, the clause versions (each
    /// `ProofId` proving its term-clause via an `assume`/`or` step), and the
    /// candidate proof carrying those `assume`/`or` leaves.
    fn seed_relaxation_clause_database(
        &self,
        roots: &[TermId],
    ) -> Option<(HashMap<u32, TermId>, Vec<(Vec<Literal>, ProofId)>, Proof)> {
        // Decompose each root into a clause of literals: a unit, or a flat
        // `(or l1 .. ln)`. Anything else -> decline (not the CNF shape).
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
        let mut next_var: u32 = 0;
        // Per root: (clause literal TERMS as they appear, their (atom, value)).
        let mut root_clauses: Vec<(Vec<TermId>, Vec<(TermId, bool)>)> =
            Vec::with_capacity(roots.len());
        for &root in roots {
            let lit_terms: Vec<TermId> = match self.ctx.terms.get(root) {
                Td::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
                    args.clone()
                }
                _ => vec![root],
            };
            let mut atoms: Vec<(TermId, bool)> = Vec::with_capacity(lit_terms.len());
            for &lit in &lit_terms {
                let av = literal_atom(&self.ctx.terms, lit)?;
                let (atom, _) = av;
                if !atom_to_var.contains_key(&atom) {
                    atom_to_var.insert(atom, next_var);
                    var_to_term.insert(next_var, atom);
                    next_var += 1;
                }
                atoms.push(av);
            }
            root_clauses.push((lit_terms, atoms));
        }

        // At least one arithmetic atom must participate; a purely Boolean UNSAT
        // is a different lane and the arith theory oracle would never fire.
        let has_arith = var_to_term.values().any(|&atom| {
            matches!(
                self.ctx.terms.get(atom),
                Td::App(Symbol::Named(name), args)
                    if args.len() == 2
                        && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
            )
        });
        if !has_arith {
            return None;
        }

        // Build the candidate: `assume` each root; expose each disjunction's flat
        // clause via an Alethe `or` step so each clause version's `ProofId` proves
        // exactly its term-clause.
        let mut candidate = Proof::new();
        let mut clause_versions: Vec<(Vec<Literal>, ProofId)> =
            Vec::with_capacity(root_clauses.len());
        for ((lit_terms, atoms), &root) in root_clauses.iter().zip(roots.iter()) {
            let assume_id = candidate.add_assume(root, None);
            let sat_clause: Vec<Literal> = atoms
                .iter()
                .map(|&(atom, value)| {
                    let var = Variable::new(atom_to_var[&atom]);
                    if value {
                        Literal::positive(var)
                    } else {
                        Literal::negative(var)
                    }
                })
                .collect();
            let proof_id = if lit_terms.len() == 1 {
                assume_id
            } else {
                candidate.add_step(ProofStep::Step {
                    rule: AletheRule::Or,
                    clause: lit_terms.clone(),
                    premises: vec![assume_id],
                    args: vec![],
                })
            };
            clause_versions.push((sat_clause, proof_id));
        }

        Some((var_to_term, clause_versions, candidate))
    }
}
