// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Genuine Farkas reconstruction for a formula-level arithmetic-ITE UNSAT.
//!
//! Sibling of [`super::relaxation_farkas`]. Where that pass rebuilds a flat-CNF
//! relaxation refutation, this one handles a QF_LIA/QF_LRA UNSAT whose conflict
//! runs through a formula-level `ite` over linear atoms (e.g. `(ite c (= I a)
//! (= I b))` with a nonnegativity/successor contradiction) and whose exported
//! proof collapsed onto `trust` leaves — a preprocessing-lifted ITE the
//! provenance-surgery cascades cannot rebuild because the substituted trust
//! terms no longer match the authored surface, and because the master conflict
//! (which fuses the ITE, its bounds, and the contradiction) has no single-leaf
//! planner.
//!
//! Covered shapes (each addition below is derivation-only — every extra clause
//! is proved from an authored `assume` by checker-validated steps before it is
//! seeded, and the whole candidate must still re-check strict-complete):
//! * a TOP-LEVEL CONJUNCTION root: each conjunct is derived by an `and_pos`
//!   tautology resolved against the root's `assume`, then classified like an
//!   authored root of its own (recursively for nested conjunctions). This is
//!   the deductive-checks consumer's exact spelling — one `(and …)` assertion carrying
//!   bounds, the ITEs, and the refuted claim (#wrapping-refutation-t5);
//! * NESTED formula-level ITEs (`(ite c1 A (ite c2 B C))`, the two-sided
//!   wrapping-arithmetic model): the ITE tree is peeled into PATH clauses via
//!   the premise-free `ite_pos1`/`ite_pos2` tautologies, each resolved on its
//!   ITE literal, so only ITE-free clauses over usable atoms enter the search
//!   database;
//! * a refuted arithmetic EQUALITY (`(not (= a b))`, the negated roundtrip
//!   identity): the branch conflicts rest on the disequality, which the LRA
//!   oracle deliberately never asserts. The `la_disequality` tautology
//!   `(or (= a b) (not (<= a b)) (not (<= b a)))`, clausified and resolved
//!   against the unit disequality, seeds the two complementary bounds the
//!   oracle CAN consume;
//! * a SUBSTITUTION-DERIVED formula-level ITE root: preprocessing rewrote the
//!   authored premise, so the canonical root no longer prints as any authored
//!   assertion and may not be `assume`d. Its exact recorded preprocessing
//!   sources instead supply a provenance ITE lift whose checked branch
//!   derivation seeds the two implication clauses.
//!
//! Every `assume` this pass rebuilds is AUTHENTICATED before it enters the
//! candidate. In PARSE mode (a script parser retained the authored surface) a
//! conjunction or `or` root must decompose, positionally, exactly as the
//! parsed original spells it (the seeded `and_pos`/`or` steps are positional),
//! and a formula-level ITE root must either match its authored surface
//! directly or ride the provenance lift above. In NATIVE mode (an embedded
//! consumer asserted terms through the API — no text, no parse, so no surface
//! exists anywhere) the assertion stack IS the original problem: a root
//! authenticates by TermId identity with an original-stack entry (the exact
//! terms the consumer asserted — `proof_original_problem_assertions`), its
//! canonical rendering is the surface (so positional decomposition is
//! trivially faithful), and any root that is NOT itself an asserted term (a
//! rewrite/substitution product, whose lift would need parse provenance)
//! declines individually. Derived facts need no such check in either mode —
//! they carry checker-validated derivations from an authenticated `assume`.

// #8529: Use deterministic hash maps/sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData as Td;
use ay_core::{Proof, ProofId, Sort, Symbol, TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;
use ay_sat::{Literal, Variable};

use crate::executor::proof_trust_surgery_provenance::{OriginalSourceIndex, SurgeryPlanningBudget};
use crate::executor::Executor;

mod fact_classification;
mod seeded_proof;

/// Upper bound on the authored-assertion count this pass will attempt to
/// reconstruct. The arithmetic-ITE conflicts are small; a larger assertion set
/// is left for the fail-closed trust fallback rather than seeding a costly
/// bounded DPLL(T) scan.
const MAX_ARITH_ITE_ROOTS: usize = 512;

/// Total classification/derivation visits per seeding attempt. Conjunction
/// flattening and ITE peeling are both worklist-driven; exceeding the budget
/// stops seeding further facts (a SUBSET of the derivable clauses is always
/// sound — at worst the closer finds the database satisfiable and declines).
const MAX_SEED_WORK: usize = 4_096;

/// Conjunction-nesting depth bound for the recursive `and_pos` flattening.
const MAX_SEED_DEPTH: usize = 16;

/// Cap on the clauses one `(or …)`-of-conjunctions distribution may emit — the
/// size of the cross-product of per-disjunct conjunct choices. The deductive-checks
/// panic-freedom shape is `2 × 2 = 4`; anything past this bound is left to the
/// fail-closed trust fallback rather than blown up into a costly database
/// (seeding a SUBSET of the authorized consequences is always sound, so an
/// over-budget disjunction simply seeds nothing).
const MAX_OR_DISTRIBUTION_CLAUSES: usize = 32;

/// Cap on the conjuncts of a single conjunctive disjunct considered for that
/// distribution.
const MAX_OR_DISTRIBUTION_CHOICES: usize = 8;

/// A propositional atom usable in the seeded clause database: a Boolean-var
/// atom, or a binary `</<=/>/>=/=` comparison whose BOTH operands are `ite`-free.
/// Returns `(atom, value)` with `value = false` for a single leading `not`.
///
/// The `ite`-free requirement is load-bearing: it declines a term-level ITE
/// equality such as `(= W (ite K 0 1))`, which must never be handed to the
/// linear-arithmetic oracle as if it were a linear atom. Its already-lifted
/// formula-level sibling `(ite K (= W 0) (= W 1))` is seeded as an ITE instead.
fn usable_atom(terms: &TermStore, lit: TermId) -> Option<(TermId, bool)> {
    let (atom, value) = match terms.get(lit) {
        Td::Not(inner) => (*inner, false),
        _ => (lit, true),
    };
    let usable = match terms.get(atom) {
        Td::Var(..) => matches!(terms.sort(atom), Sort::Bool),
        Td::App(Symbol::Named(name), args) => {
            args.len() == 2
                && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
                && args.iter().all(|&operand| ite_free(terms, operand))
        }
        _ => false,
    };
    usable.then_some((atom, value))
}

/// Whether `term`'s subtree is free of any `ite`, `let`, or quantifier — i.e.
/// a plain first-order arithmetic/Boolean expression the strict Farkas checker
/// and the LRA oracle can both reason over directly.
fn ite_free(terms: &TermStore, term: TermId) -> bool {
    // Every call is downstream of the aggregate, depth-bounded root preflight
    // in `seed_arith_ite_clause_database`; the visited traversal avoids both
    // call-stack growth and repeated shared-DAG work.
    let mut pending = vec![term];
    let mut visited = HashSet::default();
    while let Some(term) = pending.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            Td::Const(_) | Td::Var(..) => {}
            Td::Not(inner) => pending.push(*inner),
            Td::App(_, args) => pending.extend(args.iter().copied()),
            // `ite`, `let`, and binders are outside the linear-atom fragment.
            _ => return false,
        }
    }
    true
}

/// Whether `atom` is a genuine linear-arithmetic comparison (`< <= > >= =`)
/// over Int/Real operands — as opposed to a Boolean equality like `(= K true)`.
fn is_arith_atom(terms: &TermStore, atom: TermId) -> bool {
    match terms.get(atom) {
        Td::App(Symbol::Named(name), args) => {
            args.len() == 2
                && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
        }
        _ => false,
    }
}

/// Interning state plus the clause database under construction. One value per
/// seeding attempt; every helper threads it explicitly.
#[derive(Default)]
struct ArithIteSeeding {
    atom_to_var: HashMap<TermId, u32>,
    var_to_term: HashMap<u32, TermId>,
    next_var: u32,
    clause_versions: Vec<(Vec<Literal>, ProofId)>,
    /// Deduplicated authored `assume` steps: a provenance plan's supports can
    /// coincide with other seeded roots, and each authored term must be
    /// assumed at most once.
    authored_assumes: HashMap<TermId, ProofId>,
    /// At least one formula-level ITE contributed a path clause — this pass's
    /// whole purpose; the entry gate declines without one.
    seeded_ite: bool,
    work: usize,
}

impl ArithIteSeeding {
    fn intern(&mut self, atom: TermId) -> u32 {
        if let Some(&var) = self.atom_to_var.get(&atom) {
            return var;
        }
        let var = self.next_var;
        self.next_var += 1;
        self.atom_to_var.insert(atom, var);
        self.var_to_term.insert(var, atom);
        var
    }

    /// Add the authored `assume` for `term` once; later requests reuse it.
    fn assume_once(&mut self, proof: &mut Proof, term: TermId) -> ProofId {
        if let Some(&id) = self.authored_assumes.get(&term) {
            return id;
        }
        let id = proof.add_assume(term, None);
        self.authored_assumes.insert(term, id);
        id
    }

    /// Charge one unit of classification/derivation work; `false` means the
    /// budget is exhausted and the caller must stop seeding (fail-closed).
    fn charge(&mut self) -> bool {
        self.work += 1;
        self.work <= MAX_SEED_WORK
    }

    /// Map a term clause onto interned SAT literals, or `None` when any
    /// literal is not a usable atom (the clause is then simply not seeded).
    fn sat_clause(&mut self, terms: &TermStore, lit_terms: &[TermId]) -> Option<Vec<Literal>> {
        let mut sat: Vec<Literal> = Vec::with_capacity(lit_terms.len());
        for &lit in lit_terms {
            let (atom, value) = usable_atom(terms, lit)?;
            let var = self.intern(atom);
            let literal = mk_lit(var, value);
            // Duplicates would double-count as "two unassigned literals" in the
            // closer's unit propagation; the term clause was deduplicated by the
            // callers, so a SAT-level duplicate only arises from two distinct
            // spellings of one atom and is safe to drop.
            if !sat.contains(&literal) {
                sat.push(literal);
            }
        }
        Some(sat)
    }
}

fn mk_lit(var: u32, value: bool) -> Literal {
    let variable = Variable::new(var);
    if value {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

/// The authorized authored surface for one seeding attempt: every root
/// `assume` must authenticate against it before entering the candidate.
struct RootAuthentication<'a> {
    originals: &'a [(TermId, FrontendTerm)],
    source_index: OriginalSourceIndex,
    planning: SurgeryPlanningBudget,
    /// `Some` in NATIVE mode (no parsed surface exists — every assertion came
    /// through the API): the ORIGINAL problem assertion stack. A root then
    /// authenticates by TermId identity — it must literally BE a term the
    /// consumer asserted — and the surface/provenance lanes are disabled.
    /// `None` in parse mode: the parsed-surface checks above are the only
    /// authentication.
    native_asserted: Option<HashSet<TermId>>,
}

impl RootAuthentication<'_> {
    /// Native-mode identity verdict for `root`: `Some(is_original_assertion)`
    /// in native mode, `None` in parse mode (surface authentication decides).
    fn native_root_identity(&self, root: TermId) -> Option<bool> {
        self.native_asserted
            .as_ref()
            .map(|live| live.contains(&root))
    }
}

impl Executor {
    /// Rebuild a genuine, strict-checkable Farkas refutation for a formula-level
    /// arithmetic-ITE UNSAT whose proof otherwise collapsed onto `trust` leaves.
    ///
    /// The authored assertions carry a formula-level `ite` over linear branch
    /// facts (`(ite c (= I a) (= I b))`) plus linear bounds and a linear
    /// contradiction — possibly all spelled as ONE top-level conjunction, with
    /// the ITEs nested two deep and the contradiction a refuted equality (the
    /// deductive-checks wrapping-arithmetic model). AY computes the correct `unsat`,
    /// but preprocessing substitutes the derived variables away, so the
    /// exported refutation rides on `trust` steps — none of which any authored /
    /// provenance-surgery cascade can rebuild.
    ///
    /// This pass reconstructs the honest proof directly from the authorized
    /// assertions. Conjunction roots are flattened conjunct-by-conjunct
    /// (`and_pos` + resolution), each formula-level ITE tree contributes its
    /// GENUINE path clauses (`ite_pos1`/`ite_pos2` tautologies resolved on the
    /// ITE literal), every linear bound/contradiction is a unit or `(or …)`
    /// clause, and a refuted arithmetic equality additionally seeds its
    /// `la_disequality` bound split. It then hands the database to the same
    /// bounded DPLL(T) closer the trace-driven pipeline uses: it case-splits
    /// the ITE conditions, and at each propositional stall the LRA oracle
    /// certifies the branch conflict with a fresh Farkas certificate, folding
    /// everything into ordinary `Resolution` steps over an
    /// `la_generic`/`lia_generic`-printable lemma.
    ///
    /// SOUNDNESS / fail-closed at every gate:
    /// * runs ONLY when the current proof still rides on a `trust`/`hole`
    ///   fallback, so an already-certified UNSAT is left byte-identical;
    /// * an authored root is `assume`d only after it authenticates: in parse
    ///   mode against the parsed original surface (positional `and`/`or`
    ///   decomposition, direct ITE surface match), with a substitution-derived
    ///   ITE instead riding a provenance lift derived from its exact authored
    ///   sources; in native mode (no parsed surface exists) by TermId
    ///   identity with an original-stack entry (the exact terms the consumer
    ///   asserted), every non-identical root declining individually;
    /// * every seeded clause proves EXACTLY its derivation from an authored
    ///   assertion (`assume`, plus checked `and_pos`/`ite_pos1`/`ite_pos2`/
    ///   `la_disequality`/`or`/`resolution` steps), so no assumption is
    ///   invented; term-level ITE equalities and any other unusable fact are
    ///   simply not seeded — a SUBSET of the authorized consequences, always
    ///   sound;
    /// * the assumptions are the exact strict-proof scope, so every rebuilt
    ///   `assume` is authorized;
    /// * the candidate REPLACES the trust proof ONLY after it independently
    ///   re-checks strict-complete (the strict checker re-derives every Farkas
    ///   combination and every tautology/resolution step); any gap leaves the
    ///   original proof untouched.
    pub(crate) fn rebuild_arith_ite_case_split_farkas(&mut self, proof: &mut Proof) {
        // (0) Only repair a proof that still rides on a `trust`/`hole` fallback.
        if ay_proof::terminal_trust_report(proof).is_trust_free() {
            return;
        }

        // (1) Authorized roots = the exact scope strict checking validates
        // assumptions against, so every rebuilt `assume` stays in problem scope.
        let roots = self.complete_problem_assertions_for_strict_proof();
        if roots.is_empty() || roots.len() > MAX_ARITH_ITE_ROOTS {
            return;
        }

        // (2) Seed a clause database from the arithmetic-ITE roots. Declines
        // (fail-closed) unless at least one formula-level ITE and one genuine
        // arithmetic atom participate.
        let Some((var_to_term, clause_versions, mut candidate)) =
            self.seed_arith_ite_clause_database(&roots)
        else {
            return;
        };

        // (3) Hand the seeded clause database to the bounded DPLL(T) closer.
        let empty_id = {
            // Best-effort budget for synthesized-default certificates (#A2b):
            // explicit in-script proof requests remain unbounded.
            let script_demands_proof = matches!(
                self.ctx.get_option("produce-proofs"),
                Some(ay_frontend::OptionValue::Bool(true))
            );
            let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
            if !script_demands_proof {
                manager.set_step_budget(self.proof_reconstruction_step_budget);
            }
            manager.close_empty_over_seeded_clauses(&clause_versions, &mut candidate)
        };
        let Some(empty_id) = empty_id else {
            return;
        };

        // (4) Prune to the empty-clause cone and accept ONLY on a strict,
        // complete re-check. The strict checker is the sole arbiter.
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
    /// the arithmetic-ITE roots, for [`Self::rebuild_arith_ite_case_split_farkas`].
    ///
    /// Returns `None` (declines fail-closed) unless at least one formula-level
    /// ITE contributed a path clause and at least one genuine linear-arithmetic
    /// atom participates. Facts that are neither a conjunction, a formula-level
    /// ITE, nor a flat clause of usable atoms (e.g. a term-level ITE equality)
    /// are skipped, not fatal: seeding a subset of the authorized consequences
    /// is always sound.
    fn seed_arith_ite_clause_database(
        &mut self,
        roots: &[TermId],
    ) -> Option<(HashMap<u32, TermId>, Vec<(Vec<Literal>, ProofId)>, Proof)> {
        let parsed_assertions = self.ctx.assertions_parsed().to_vec();
        // NATIVE mode: every retained parsed slot is the API sentinel (or none
        // was retained at all) — no authored surface exists anywhere, so the
        // assertion stack IS the original problem and roots authenticate by
        // TermId identity against it. Any genuine parsed surface keeps the
        // parse-mode zip below exactly as before (a mixed session therefore
        // stays parse-mode, where a sentinel slot fails surface checks and
        // that root is skipped, fail-closed).
        let native_mode = parsed_assertions
            .iter()
            .all(crate::executor::proof_original_rebuild::is_api_placeholder);
        let (originals, native_asserted): (Vec<(TermId, FrontendTerm)>, Option<HashSet<TermId>>) =
            if native_mode {
                // The native ORIGINAL stack: exactly the terms the consumer
                // asserted. `proof_original_problem_assertions` prefers the
                // provenance snapshot because a core-tracking redirect or
                // in-place preprocessing may have emptied/rewritten the live
                // `ctx.assertions` by proof-export time; preprocessing
                // products and injected axioms never enter this set.
                (
                    Vec::new(),
                    Some(
                        self.proof_original_problem_assertions()
                            .into_iter()
                            .collect(),
                    ),
                )
            } else {
                let original_assertions = self.proof_original_problem_assertions();
                if original_assertions.len() != parsed_assertions.len() {
                    return None;
                }
                let originals: Vec<(TermId, FrontendTerm)> = original_assertions
                    .into_iter()
                    .zip(parsed_assertions)
                    .collect();
                (originals, None)
            };
        let source_index = OriginalSourceIndex::new(&originals);
        if !source_index.is_valid() {
            return None;
        }
        let mut planning = SurgeryPlanningBudget::new();
        if !planning.spend_terms(&self.ctx.terms, roots) {
            return None;
        }
        let mut auth = RootAuthentication {
            originals: &originals,
            source_index,
            planning,
            native_asserted,
        };

        let mut seeding = ArithIteSeeding::default();
        let mut candidate = Proof::new();
        let mut seen_roots: HashMap<TermId, ()> = HashMap::default();

        for &root in roots {
            // Deduplicate exact-identical roots: repeated normalized/original
            // spellings would only bloat the candidate.
            if seen_roots.insert(root, ()).is_some() {
                continue;
            }
            if !self.seed_fact_clauses(&mut seeding, &mut candidate, &mut auth, root, None, 0) {
                // A planned provenance emission failed mid-candidate: decline
                // the whole attempt rather than certify around a broken lane.
                return None;
            }
        }

        // Require at least one formula-level ITE (this pass's whole purpose) and
        // at least one genuine arithmetic atom (a purely Boolean case is a
        // different lane and the arith oracle would never fire).
        if !seeding.seeded_ite {
            return None;
        }
        if !seeding
            .var_to_term
            .values()
            .any(|&atom| is_arith_atom(&self.ctx.terms, atom))
        {
            return None;
        }

        Some((seeding.var_to_term, seeding.clause_versions, candidate))
    }
}
